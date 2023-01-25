\documentclass[a4paper]{article}
\usepackage[a4paper,left=3cm,right=2cm,top=2.5cm,bottom=2.5cm]{geometry}
\usepackage[sfdefault, book, lf]{FiraSans} % lf - lined numbers
\usepackage[colorlinks=true]{hyperref}
\usepackage{graphicx}
\usepackage{cp2223t}
\usepackage{subcaption}
\usepackage{adjustbox}
\usepackage[indent=12pt]{parskip}

%================= lhs2tex=====================================================%
%include polycode.fmt
%format (div (x)(y)) = x "\div " y
%format succ = "\succ "
%format ==> = "\Longrightarrow "
%format map = "\map "
%format length = "\length "
%format fst = "\p1"
%format p1  = "\p1"
%format snd = "\p2"
%format p2  = "\p2"
%format Left = "i_1"
%format Right = "i_2"
%format i1 = "i_1"
%format i2 = "i_2"
%format >< = "\times"
%format >|<  = "\bowtie "
%format |-> = "\mapsto"
%format . = "\comp "
%format .=?=. = "\mathbin{\stackrel{\mathrm{?}}{=}}"
%format -|- = "+"
%format conc = "\mathsf{conc}"
%format summation = "{\sum}"
%format (either (a) (b)) = "\alt{" a "}{" b "}"
%format (frac (a) (b)) = "\frac{" a "}{" b "}"
%format (uncurry f) = "\uncurry{" f "}"
%format (const (f)) = "\underline{" f "}"
%format (lcbr (x)(y)) = "\begin{lcbr}" x "\\" y "\end{lcbr}"
%format (lcbr3 (x)(y)(z)) = "\begin{lcbr}" x "\\" y "\\" z "\end{lcbr}"
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (for (f) (i)) = "\for{" f "}\ {" i "}"
%format <$> = "\mathbin{\mathopen{\langle}\$\mathclose{\rangle}}"
%format Either a b = a "+" b
%format fmap = "\mathsf{fmap}"
%format NA   = "\textsc{na}"
%format NB   = "\textbf{NB}"
%format inT = "\mathsf{in}"
%format outT = "\mathsf{out}"
%format outLTree = "\mathsf{out}_{\tiny\ \textit{LTree}}"
%format inLTree = "\mathsf{in}_{\tiny\ \textit{LTree}}"
%format inFTree = "\mathsf{in}_{\tiny\ \textit{FTree}}"
%format outFTree = "\mathsf{out}_{\tiny\ \textit{FTree}}"
%format inExp = "\mathsf{in}_{\tiny\ \textit{Exp}}"
%format outExp = "\mathsf{out}_{\tiny\ \textit{Exp}}"
%format Null = "1"
%format (Prod (a) (b)) = a >< b
%format fF = "\fun F "
%format l2 = "l_2 "
%format Dist = "\fun{Dist}"
%format IO = "\fun{IO}"
%format LTree = "{\LTree}"
%format FTree = "{\FTree}"
%format inNat = "\mathsf{in}"
%format (cata (f)) = "\llparenthesis\, " f "\,\rrparenthesis"
%format (cataNat (g)) = "\llparenthesis\, " g "\,\rrparenthesis"
%format (cataList (g)) = "\llparenthesis\, " g "\,\rrparenthesis"
%format (cataLTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (cataFTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (cataRose (x)) = "\llparenthesis\, " x "\,\rrparenthesis_\textit{\tiny R}"
%format (cataExp (x)) = "\llparenthesis\, " x "\,\rrparenthesis_\textit{\tiny Exp}"
%format (ana (g)) = "\ana{" g "}"
%format (anaList (g)) = "\anaList{" g "}"
%format (anaLTree (g)) = "\lanabracket\;\!" g "\;\!\ranabracket"
%format (anaRose (g)) = "\lanabracket\;\!" g "\;\!\ranabracket_\textit{\tiny R}"
%format (anaExp (g)) = "\lanabracket\;\!" g "\;\!\ranabracket_\textit{\tiny Exp}"
%format (hylo (g) (h)) = "\llbracket\, " g ",\," h "\,\rrbracket"
%format (hyloRose (g) (h)) = "\llbracket\, " g ",\," h "\,\rrbracket_\textit{\tiny R}"
%format (hyloExp (g) (h)) = "\llbracket\, " g ",\," h "\,\rrbracket_\textit{\tiny Exp}"
%format Nat0 = "\N_0"
%format Rational = "\Q "
%format toRational = " to_\Q "
%format fromRational = " from_\Q "
%format muB = "\mu "
%format (frac (n)(m)) = "\frac{" n "}{" m "}"
%format (fac (n)) = "{" n "!}"
%format (underbrace (t) (p)) = "\underbrace{" t "}_{" p "}"
%format matrix = "matrix "
%format `ominus` = "\mathbin{\ominus}"
%format <-> = "{\,\leftrightarrow\,}"
%format <|> = "{\,\updownarrow\,}"
%format `minusNat`= "\mathbin{-}"
%format ==> = "\Rightarrow"
%format .==>. = "\Rightarrow"
%format .<==>. = "\Leftrightarrow"
%format .==. = "\equiv"
%format .<=. = "\leq"
%format .&&&. = "\wedge"
%format cdots = "\cdots "
%format pi = "\pi "
%format (curry (f)) = "\overline{" f "}"
%format delta = "\Delta "
%format (plus (f)(g)) = "{" f "}\plus{" g "}"
%format ++ = "\mathbin{+\!\!\!+}"
%format Integer  = "\mathbb{Z}"
%format (Cp.cond (p) (f) (g)) = "\mcond{" p "}{" f "}{" g "}"
\def\plus{\mathbin{\dagger}}
%format square (x) = x "^2"
%format a1 = "a_1 " 
%format a2 = "a_2 " 
%format a3 = "a_3 " 
%format a4 = "a_4 " 
%format b1 = "b_1 " 
%format b2 = "b_2 " 
%format b3 = "b_3 " 
%format b4 = "b_4 " 
%format c1 = "c_1 " 
%format c2 = "c_2 " 
%format c3 = "c_3 " 
%format c4 = "c_4 " 
%format d1 = "d_1 " 
%format d2 = "d_2 " 
%format d3 = "d_3 " 
%format d4 = "d_4 " 
%format r1 = "r_1 " 
%format r2 = "r_2 " 
%format s1 = "s_1 " 
%format s2 = "s_2 " 
%format e1 = "e_1 " 
%format e2 = "e_2 " 
\def\kcomp{\mathbin{\bullet}}
%format (kcomp (f) (g)) = f "\kcomp " g
%format .! = "\kcomp"
%---------------------------------------------------------------------------

\title{
          \textbf{Cálculo de Programas}
\\
          Trabalho Prático
\\
          LEI --- 2022/23
}

\author{
          \dium
\\
          Universidade do Minho
}


\date\mydate

\makeindex
\newcommand{\rn}[1]{\textcolor{Red}{#1}}
\begin{document}
\emergencystretch 3em
%\sloppy

\maketitle

\begin{center}\large
\begin{tabular}{ll}
Grupo 48. & 99 (preencher)
\\\hline
a95437 & Beatriz Ribeiro Monteiro
\\
a95719 & João Pedro Machado Ribeiro
\\
a96386 & João Miguel Rodrigues da Cunha
\\
a96626 & João Carlos Fernandes Novais
\end{tabular}
\end{center}

\section*{Preâmbulo}

\CP\ tem como objectivo principal ensinar
a progra\-mação de computadores como uma disciplina científica. Para isso
parte-se de um repertório de \emph{combinadores} que formam uma álgebra da
programação (conjunto de leis universais e seus corolários) e usam-se esses
combinadores para construir programas \emph{composicionalmente}, isto é,
agregando programas já existentes.

Na sequência pedagógica dos planos de estudo dos cursos que têm
esta disciplina, opta-se pela aplicação deste método à programação
em \Haskell\ (sem prejuízo da sua aplicação a outras linguagens
funcionais). Assim, o presente trabalho prático coloca os
alunos perante problemas concretos que deverão ser implementados em
\Haskell.  Há ainda um outro objectivo: o de ensinar a documentar
programas, a validá-los e a produzir textos técnico-científicos de
qualidade.

Antes de abodarem os problemas propostos no trabalho, os grupos devem ler
com atenção o anexo \ref{sec:documentacao} onde encontrarão as instruções
relativas ao sofware a instalar, etc.

%if False
\begin{code}
{-# OPTIONS_GHC -XNPlusKPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances #-}
module Main where
import Cp
import List hiding (fac)
import NEList (out)
import Exp
import Nat hiding (aux)
import LTree
import Rose hiding (g)
import Probability
import Data.List hiding (find)
import Data.List.Split hiding (split,chunksOf) 
import Svg hiding (for,wrap)
import Control.Concurrent
import Cp2223data

main = undefined
instance Strong Dist
\end{code}
%endif

\Problema
Suponha-se uma sequência numérica semelhante à sequência de Fibonacci tal
que cada termo subsequente aos três primeiros corresponde à soma dos três
anteriores, sujeitos aos coeficientes |a|, |b| e |c|:
\begin{code}
f a b c 0 = 0
f a b c 1 = 1
f a b c 2 = 1
f a b c (n+3) = a * f a b c (n+2) + b * f a b c (n+1) + c * f a b c n

\end{code}
Assim, por exemplo, |f 1 1 1| irá dar como resultado a sequência:
\begin{spec}
1, 1, 2, 4, 7, 13, 24, 44, 81, 149, ...
\end{spec}
|f 1 2 3| irá gerar a sequência:
\begin{spec}
1,1,3,8,17,42,100,235,561,1331, ...
\end{spec}
etc.

A definição de |f| dada é muito ineficiente, tendo uma degradação do tempo
de execução exponencial.
Pretende-se otimizar a função dada convertendo-a para um ciclo \textit{for}.
Recorrendo à lei de recursividade mútua, calcule |loop| e |initial| em
\begin{code}
fbl a b c = wrap . (for ((loop a b c)) initial)
\end{code}
por forma a |f| e |fbl| serem (matematicamente) a mesma função. 
Para tal, poderá usar a regra prática explicada no anexo \ref{sec:mr}.

\textbf{Valorização}: apresente testes de \textit{performance} que mostrem
quão mais rápida é |fbl| quando comparada com |f|.

\Problema
Pretende-se vir a classificar os conteúdos programáticos de todas as
\href{https://web.di.uminho.pt/sitedi/ucs/}{UCs} lecionadas no \dium\ de
acordo com o \href{https://dl.acm.org/ccs}{ACM Computing Classification System}.
A listagem da taxonomia desse sistema está disponível no ficheiro
\texttt{Cp2223data}, 
começando com
\begin{spec}
acm_ccs = [  "CCS",
             "    General and reference",
             "        Document types",
             "            Surveys and overviews",
             "            Reference works",
             "            General conference proceedings",
             "            Biographies",
             "            General literature",
             "            Computing standards, RFCs and guidelines",
             "        Cross-computing tools and techniques",
\end{spec}
(10 primeiros ítens) etc., etc.\footnote{Informação obtida a partir do site
\href{https://dl.acm.org/ccs}{ACM CCS} selecionando \emph{Flat View}.}

Pretende-se representar a mesma informação sob a forma de uma árvore de expressão,
usando para isso a biblioteca \Exp\ que consta do material padagógico da disciplina e
que vai incluída no zip do projecto, por  ser mais conveniente para os alunos.

\begin{enumerate}
\item Comece por definir a função de conversão do texto dado em |acm_ccs|
(uma lista de \emph{strings}) para uma tal árvore como um anamorfismo de \Exp:
%
\begin{code}
tax :: [String] -> Exp String String
tax = anaExp gene
\end{code}
Ou seja, defina o |gene| do anamorfismo, 
tendo em conta o seguinte diagrama\footnote{|S| abrevia |String|.}:
\begin{eqnarray*}
\xymatrix{
  |Exp S S| & & S + S \times (|Exp S S|)^*\ar[ll]_{|inExp|} \\
  S^*\ar@@/_1.5pc/[rr]_{|gene|}\ar[r]^(0.35){|out|}\ar[u]^{|tax|} & S + S \times S^*\ar[r]^(0.45){\cdots} & S + S \times (S^*)^*\ar[u]_{id + id \times tax^*}
}
\end{eqnarray*}
Para isso, tome em atenção que cada nível da hierarquia é, em |acm_ccs|,
marcado pela indentação de 4 espaços adicionais --- como se mostra no fragmento acima.

Na figura \ref{fig:P1} mostra-se a representação gráfica da árvore de tipo \Exp\ que representa o fragmento de |acm_ccs| mostrado acima.

\begin{figure}[ht!]
\centering
\begin{tikzpicture}
[-,every node/.style={shape=rectangle,inner sep=3pt,draw}]
\footnotesize
\node {CSS} [edge from parent fork down]
  [sibling distance=4cm]
  child {node [align=center] {General and\\reference}
    [sibling distance=4cm]
    child {node {Document types}
      [sibling distance=2.25cm]
      child {node [align=center] {Surveys and\\overviews}}
      child {node [align=center] {Reference\\works}}
      child {node [align=center] {General\\conference\\proceedings}}
      child {node [align=center] {Biographies}}
      child {node [align=center] {General\\literature}}
      child {node [align=center, xshift=0.75cm] {Computing standards,\\RFCs and\\guidelines}}
    }
    child {node [align=center] {Cross-computing tools and\\techniques}}
  }
  ;
\end{tikzpicture}
\caption{Fragmento de |acm_ccs| representado sob a forma de uma árvore do tipo \Exp.}
\label{fig:P1}
\end{figure}

\item De seguida vamos querer todos os caminhos da árvore que é gerada por |tax|,
pois a classificação de uma UC pode ser feita a qualquer nível (isto é, caminho
descendente da raiz |"CCS"| até um subnível ou folha).
\footnote{Para um exemplo de classificação de UC concreto, pf.\  ver a secção \textbf{Classificação ACM} na página
pública de \CP.}

Precisamos pois da composição de |tax| com uma função de pós-processamento |post|,
%
\begin{code}
tudo :: [String] -> [[String]]
tudo = post . tax
\end{code}
para obter o efeito que se mostra na tabela \ref{table:acmccs}.

\begin{table}[ht!]
\centering\small
\begin{center}
\begin{tabular}{||l||l||l||l||}
\hline
CCS & & & 
\\\hline
CCS & General and reference & & 
\\\hline
CCS & General and reference & Document types & 
\\\hline
CCS & General and reference & Document types & Surveys and overviews
\\\hline
CCS & General and reference & Document types & Reference works
\\\hline
CCS & General and reference & Document types & General conference proceedings
\\\hline
CCS & General and reference & Document types & Biographies
\\\hline
CCS & General and reference & Document types & General literature
\\\hline
CCS & General and reference & Cross-computing tools and techniques & 
\\\hline
\end{tabular}
\end{center}
\caption{Taxonomia ACM fechada por prefixos (10 primeiros ítens).}
\label{table:acmccs}
\end{table}

Defina a função |post :: Exp String String -> [[String]]| da forma mais económica que encontrar.
\end{enumerate}

\textbf{Sugestão}: Inspecione as bibliotecas fornecidas à procura de funções
auxiliares que possa re-utilizar para a sua solução ficar mais simples.
Não se esqueça que, para o mesmo resultado,
nesta disciplina \emph{``ganha'' quem escrever menos código}!

\textbf{Sugestão}: Para efeitos de testes intermédios não use a totalidade de |acm_ccs|,
que tem 2114 linhas! Use, por exemplo, |take 10 acm_ccs|, como se mostrou acima.

\Problema

O \sierpCarpet{tapete de Sierpinski} é uma figura geométrica \fractal\ em que um quadrado é subdividido recursivamente em sub-quadrados. A construção clássica do tapete de Sierpinski é a seguinte: assumindo um quadrado de lado |l|, este é subdivido em 9 quadrados iguais de lado |l / 3|, removendo-se o quadrado central. Este passo é depois repetido sucessivamente para cada um dos 8 sub-quadrados restantes (Fig.~\ref{fig:sierp1}).

\begin{figure}[h!]
  \centering
  \includegraphics[width=0.19\textwidth]{cp2223t_media/tapete1.png}
  \includegraphics[width=0.19\textwidth]{cp2223t_media/tapete2.png}
  \includegraphics[width=0.19\textwidth]{cp2223t_media/tapete3.png}
  \includegraphics[width=0.19\textwidth]{cp2223t_media/tapete4.png}
  \includegraphics[width=0.19\textwidth]{cp2223t_media/tapete5.png}
  \caption{Construção do tapete de Sierpinski com profundidade 5.}
  \label{fig:sierp1}
\end{figure}

\noindent
|NB|: No exemplo da fig.~\ref{fig:sierp1}, assumindo a construção clássica já referida, os quadrados estão a branco e o fundo a verde.

A complexidade deste algoritmo, em função do número de quadrados a desenhar, para uma profundidade $n$, é de $8^n$ (exponencial). No entanto, se assumirmos que os quadrados a desenhar são os que estão a verde, a complexidade é reduzida para $\sum_{i=0}^{n-1}8^i$, obtendo um ganho de $\sum_{i=1}^{n} \frac{100}{8^i} \%$. Por exemplo, para $n=5$, o ganho é de $14.28 \%$. O objetivo deste problema é a implementação do algoritmo mediante a referida otimização.
\begin{figure}[h!]
  \centering
  \includegraphics[width=0.35\textwidth]{cp2223t_media/tapete_ex}
  \caption{Tapete de Sierpinski com profundidade 2 e com os quadrados enumerados.}
  \label{fig:sierp2}
\end{figure}

Assim, seja cada quadrado descrito geometricamente pelas coordenadas do seu vértice inferior esquerdo e o comprimento do seu lado:
\begin{code}
type Square = (Point, Side)
type Side = Double
type Point = (Double, Double)
\end{code}
A estrutura recursiva de suporte à construção de tapetes de Sierpinski será uma \Rose, na qual cada nível da árvore irá guardar os quadrados de tamanho igual. Por exemplo, a construção da fig.~\ref{fig:sierp2} poderá\footnote{A ordem dos filhos não é relevante.} corresponder à árvore da figura \ref{fig:roseTreeSierp}.
\begin{figure}[ht!]
\centering
\begin{tikzpicture}
[level distance = 2cm,
level 1/.style = {sibling distance = 1.5cm},
level 2/.style = {sibling distance = 0.9cm},
]\node [draw, circle]{1}
child {node [draw, circle]{2}
child {node [draw, circle]{10}}
child {node [draw, circle]{11}}
child {node [draw, circle]{12}}
child {node [draw, circle]{13}}
child {node [draw, circle]{14}}
child {node [draw, circle]{15}}
child {node [draw, circle]{16}}
child {node [draw, circle]{17}}}
child {node [draw, circle]{3}}
child {node [draw, circle]{4}}
child {node [draw, circle]{5}}
child {node [draw, circle]{6}}
child {node [draw, circle]{7}}
child {node [draw, circle]{8}}
child {node [draw, circle]{9}};
\end{tikzpicture}
\caption{Possível árvore de suporte para a construção da fig.~\ref{fig:sierp2}.}
\label{fig:roseTreeSierp}
\end{figure}

Uma vez que o tapete é também um quadrado, o objetivo será, a partir das informações do tapete (coordenadas do vértice inferior esquerdo e comprimento do lado), desenhar o quadrado central, subdividir o tapete nos 8 sub-tapetes restantes, e voltar a desenhar, recursivamente, o quadrado nesses 8 sub-tapetes. Desta forma, cada tapete determina o seu quadrado e os seus 8 sub-tapetes. No exemplo em cima, o tapete que contém o quadrado 1 determina esse próprio quadrado e determina os sub-tapetes que contêm os quadrados 2 a 9.

Portanto, numa primeira fase, dadas as informações do tapete, é construida a árvore de suporte com todos os quadrados a desenhar, para uma determinada profundidade.
\begin{code}
squares :: (Square, Int) -> Rose Square
\end{code}
|NB|: No programa, a profundidade começa em $0$ e não em $1$.

Uma vez gerada a árvore com todos os quadrados a desenhar, é necessário extrair os quadrados para uma lista, a qual é processada pela função |drawSq|, disponibilizada no anexo \ref{sec:codigo}.
\begin{code}
rose2List :: Rose a -> [a]
\end{code}
Assim, a construção de tapetes de Sierpinski é dada por um hilomorfismo de \textit{Rose Trees}:
\begin{code}
sierpinski :: (Square, Int) -> [Square]
sierpinski = hyloRose gr2l  gsq
\end{code}
\textbf{Trabalho a fazer:}
\begin{enumerate}
    \item Definir os genes do hilomorfismo |sierpinski|.
    \item Correr
\begin{code}
sierp4 = drawSq (sierpinski (((0,0),32),3))

constructSierp5 = do drawSq (sierpinski (((0,0),32),0))
                     await
                     drawSq (sierpinski (((0,0),32),1))
                     await
                     drawSq (sierpinski (((0,0),32),2))
                     await
                     drawSq (sierpinski (((0,0),32),3))
                     await
                     drawSq (sierpinski (((0,0),32),4))
                     await
\end{code}
     \item Definir a função que apresenta a construção do tapete de Sierpinski como é apresentada em |construcaoSierp5|, mas para uma profundidade $n \in \mathbb{N}$ recebida como parâmetro.
\begin{code}
constructSierp :: Int -> IO [()]
constructSierp = present . carpets
\end{code}
\textbf{Dica}: a função |constructSierp| será um hilomorfismo de listas, cujo anamorfismo |carpets :: Int -> [[Square]]| constrói, recebendo como parâmetro a profundidade $n$, a lista com todos os tapetes de profundidade $1..n$, e o catamorfismo |present :: [[Square]] -> IO [()]| percorre a lista desenhando os tapetes e esperando 1 segundo de intervalo.
\end{enumerate}

\Problema

Este ano ocorrerá a vigésima segunda edição do Campeonato do Mundo de Futebol, organizado pela Federação Internacional de Futebol (FIFA), a decorrer no Qatar e com o jogo inaugural a 20 de Novembro.

Uma casa de apostas pretende calcular, com base numa aproximação dos \textit{rankings}\footnote{Os \textit{rankings} obtidos \href{https://www.fifa.com/fifa-world-ranking/men?dateId=id13687}{aqui} foram escalados e arredondados.} das seleções, a probabilidade de cada seleção vencer a competição.

Para isso, o diretor da casa de apostas contratou o Departamento de Informática da Universidade do Minho, que atribuiu o projeto à equipa formada pelos alunos e pelos docentes de Cálculo de Programas.

\begin{alert}
Para resolver este problema de forma simples, ele será abordado por duas fases:
\begin{enumerate}
\item versão académica sem probabilidades, em que se sabe à partida, num jogo, quem o vai vencer;
\item versão realista com probabilidades usando o mónade \textit{Dist} (distribuições probabilísticas) que vem descrito no anexo \ref{sec:probabilities}.
\end{enumerate}
A primeira versão, mais simples, deverá ajudar a construir a segunda.
\end{alert}

\subsection*{Descrição do problema}

Uma vez garantida a qualificação (já ocorrida), o campeonato consta de duas fases consecutivas no tempo:
\begin{enumerate}
\item fase de grupos;
\item fase eliminatória (ou ``mata-mata'', como é habitual dizer-se no Brasil).
\end{enumerate}

Para a fase de grupos, é feito um sorteio das 32 seleções (o qual já ocorreu para esta competição)
que as coloca em 8 grupos, 4 seleções em cada grupo.
Assim, cada grupo é uma lista de seleções.

Os grupos para o campeonato deste ano são:
\begin{code}
type Team = String
type Group = [Team]

groups :: [Group]
groups = [["Qatar", "Ecuador", "Senegal", "Netherlands"],
          ["England", "Iran", "USA", "Wales"],
          ["Argentina", "Saudi Arabia", "Mexico", "Poland"],
          ["France", "Denmark", "Tunisia", "Australia"],
          ["Spain", "Germany", "Japan", "Costa Rica"],
          ["Belgium", "Canada", "Morocco", "Croatia"],
          ["Brazil", "Serbia", "Switzerland", "Cameroon"],
          ["Portugal", "Ghana", "Uruguay", "Korea Republic"]]
\end{code}
Deste modo, \textit{groups !! 0} corresponde ao grupo A, \textit{groups !! 1} ao grupo B, e assim sucessivamente.
Nesta fase, cada seleção de cada grupo vai defrontar (uma vez) as outras do seu grupo. 

Passam para o ``mata-mata'' as duas seleções que mais pontuarem em cada grupo, obtendo pontos, por cada jogo da fase grupos, da seguinte forma:
\begin{itemize}
\item vitória --- 3 pontos;
\item empate --- 1 ponto;
\item derrota --- 0 pontos.
\end{itemize}
Como se disse, a posição final no grupo irá determinar se uma seleção avança para o ``mata-mata'' e, se avançar, que possíveis jogos terá pela frente, uma vez que a disposição das seleções está desde o início definida para esta última fase, conforme se pode ver na figura \ref{fig:wcup22}.
\begin{figure}[ht]
    \centering
    \includegraphics[scale=0.125]{cp2223t_media/wcup2022.png}
    \caption{O ``mata-mata''}
    \label{fig:wcup22}
\end{figure}

Assim, é necessário calcular os vencedores dos grupos sob uma distribuição probabilística.
Uma vez calculadas as distribuições dos vencedores, é necessário colocá-las nas folhas de uma |LTree| de forma a fazer um \textit{match} com a figura \ref{fig:wcup22}, entrando assim na fase final da competição, o tão esperado ``mata-mata''.
Para avançar nesta fase final da competição (i.e.\ subir na árvore), é preciso ganhar, quem perder é automaticamente eliminado (``mata-mata''). Quando uma seleção vence um jogo, sobe na árvore, quando perde, fica pelo caminho. Isto significa que a seleção vencedora é aquela que vence todos os jogos do ``mata-mata''.

\subsection*{Arquitetura proposta}

A visão composicional da equipa permitiu-lhe perceber desde logo que o problema podia ser dividido, independentemente da versão, probabilística ou não, em duas partes independentes --- a da fase de grupos e a do ``mata-mata''. Assim, duas sub-equipas poderiam trabalhar em paralelo, desde que se garantisse a composicionalidade das partes.
Decidiu-se que os alunos desenvolveriam a parte da fase de grupos e os docentes a do ``mata-mata''.

\subsubsection*{Versão não probabilística}
O resultado final (não probabilístico) é dado pela seguinte função:
\begin{code}
winner :: Team
winner = wcup groups

wcup = knockoutStage . groupStage 
\end{code}
A sub-equipa dos docentes já entregou a sua parte:
\begin{code}
knockoutStage = cataLTree (either id koCriteria)
\end{code}

Considere-se agora a proposta do \textit{team leader} da sub-equipa dos alunos para o desenvolvimento da fase de grupos:

\begin{bquote}
{\slshape

Vamos dividir o processo em 3 partes:
\begin{itemize}
\item gerar os jogos,
\item simular os jogos,
\item preparar o ``mata-mata'' gerando a árvore de jogos dessa fase (fig. \ref{fig:wcup22}).
\end{itemize}
Assim:
\begin{code}
groupStage :: [Group] -> LTree Team
groupStage = initKnockoutStage . simulateGroupStage . genGroupStageMatches
\end{code}

Comecemos então por definir a função |genGroupStageMatches| que gera os jogos da fase de grupos:
\begin{code}
genGroupStageMatches :: [Group] -> [[Match]]
genGroupStageMatches = map generateMatches
\end{code}
onde
\begin{code}
type Match = (Team, Team)
\end{code}
Ora, sabemos que nos foi dada a função
\begin{code}
gsCriteria :: Match -> Maybe Team
\end{code}
que, mediante um certo critério, calcula o resultado de um jogo, retornando |Nothing| em caso de empate, ou a equipa vencedora (sob o construtor |Just|). Assim, precisamos de definir a função
\begin{code}
simulateGroupStage :: [[Match]] -> [[Team]]
simulateGroupStage = map (groupWinners gsCriteria)
\end{code}
que simula a fase de grupos e dá como resultado a lista dos vencedores,
recorrendo à função |groupWinners|:
\begin{code}
groupWinners criteria = best 2 . consolidate . (>>= matchResult criteria)
\end{code}
Aqui está apenas em falta a definição da função |matchResult|.

Por fim, teremos a função |initKnockoutStage| que produzirá a |LTree| que a sub-equipa do ``mata-mata'' precisa, com as devidas posições. Esta será a composição de duas funções:
\begin{code}
initKnockoutStage = anaLTree glt . arrangement
\end{code}
}
\end{bquote}
Trabalho a fazer:
\begin{enumerate}
\item   Definir uma alternativa à função genérica |consolidate| que seja um
catamorfismo de listas:
\begin{code}
consolidate' :: (Eq a, Num b) => [(a, b)] -> [(a, b)]
consolidate' = cataList cgene
\end{code}
\item   Definir a função |matchResult :: (Match -> Maybe Team) -> Match ->
    [(Team, Int)]| que apura os pontos das equipas de um dado jogo.
\item Definir a função genérica |pairup :: Eq b => [b] -> [(b, b)]| em que
    |generateMatches| se baseia.
\item Definir o gene |glt|.
\end{enumerate}

\subsubsection*{Versão probabilística}

Nesta versão, mais realista, |gsCriteria :: Match -> (Maybe Team)| dá lugar a
\begin{code}
pgsCriteria :: Match -> Dist (Maybe Team)
\end{code}
que dá, para cada jogo, a probabilidade de cada equipa vencer ou haver um empate.
Por exemplo, há |50%| de probabilidades de Portugal empatar com a Inglaterra,
\begin{quote}
\begin{verbatim}
pgsCriteria("Portugal","England")
        Nothing  50.0%
 Just "England"  26.7%
Just "Portugal"  23.3%
\end{verbatim}
\end{quote}
etc.

O que é |Dist|? É o mónade que trata de distribuições probabilísticas e que é descrito no
anexo \ref{sec:probabilities}, página \pageref{sec:probabilities} e seguintes. O que há a fazer? Eis o que diz o vosso \emph{team leader}:

\begin{bquote}
\slshape
O que há a fazer nesta versão é, antes de mais, avaliar qual é o impacto
de |gsCriteria| virar monádica (em |Dist|) na arquitetura geral da versão
anterior. Há que reduzir esse impacto ao mínimo, escrevendo-se tão pouco código
quanto possível!
\end{bquote}

Todos relembraram algo que tinham aprendido nas aulas teóricas a respeito
da ``monadificação'' do código: há que reutilizar o código da versão anterior,
monadificando-o.

Para distinguir as duas versões decidiu-se afixar o prefixo `p'  para identificar
uma função que passou a ser monádica.

A sub-equipa dos docentes fez entretanto a monadificação da sua parte:
\begin{spec}
pwinner :: Dist Team
pwinner = pwcup groups

pwcup = pknockoutStage .! pgroupStage 
\end{spec}
E entregou ainda a versão probabilística do ``mata-mata'':
\begin{code}
pknockoutStage = mcataLTree' (either return pkoCriteria)

mcataLTree' g = k where
        k (Leaf a) = g1 a
        k (Fork(x,y)) = mmbin g2 (k x, k y)
        g1 = g . i1
        g2 = g . i2
\end{code}
A sub-equipa dos alunos também já adiantou trabalho,
\begin{code}
pgroupStage = pinitKnockoutStage .! psimulateGroupStage . genGroupStageMatches
\end{code}
mas faltam ainda |pinitKnockoutStage| e |pgroupWinners|, esta usada em |psimulateGroupStage|,
que é dada em anexo. 

Trabalho a fazer:
\begin{itemize}
\item   Definir as funções que ainda não estão implementadas nesta versão.
\item   \textbf{Valorização}: experimentar com outros critérios de ``ranking'' das equipas.
\end{itemize}

\begin{alert}
\textbf{Importante}: (a) código adicional terá que ser colocado no anexo
\ref{sec:resolucao}, obrigatoriamente; (b) todo o código que é dado não pode
ser alterado.
\end{alert}

\part*{Anexos}

\appendix

\section{Documentação para realizar o trabalho}
\label{sec:documentacao}
Para cumprir de forma integrada os objectivos do trabalho vamos recorrer
a uma técnica de programa\-ção dita
``\litp{literária}'' \cite{Kn92}, cujo princípio base é o seguinte:
%
\begin{quote}\em Um programa e a sua documentação devem coincidir.
\end{quote}
%
Por outras palavras, o código fonte e a documentação de um
programa deverão estar no mesmo ficheiro.

O ficheiro \texttt{cp2223t.pdf} que está a ler é já um exemplo de
\litp{programação literária}: foi gerado a partir do texto fonte
\texttt{cp2223t.lhs}\footnote{O sufixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrará no
\MaterialPedagogico\ desta disciplina descompactando o ficheiro
\texttt{cp2223t.zip} e executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2223t.lhs > cp2223t.tex
    $ pdflatex cp2223t
\end{Verbatim}
em que \href{https://hackage.haskell.org/package/lhs2tex}{\texttt\LhsToTeX} é
um pré-processador que faz ``pretty printing''
de código Haskell em \Latex\ e que deve desde já instalar utilizando o
utiliário \href{https://www.haskell.org/cabal/}{cabal} disponível em \href{https://www.haskell.org}{haskell.org}.

Por outro lado, o mesmo ficheiro \texttt{cp2223t.lhs} é executável e contém
o ``kit'' básico, escrito em \Haskell, para realizar o trabalho. Basta executar
\begin{Verbatim}[fontsize=\small]
    $ ghci cp2223t.lhs
\end{Verbatim}

\noindent Abra o ficheiro \texttt{cp2223t.lhs} no seu editor de texto preferido
e verifique que assim é: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
é seleccionado pelo \GHCi\ para ser executado.

\subsection{Como realizar o trabalho}
Este trabalho teórico-prático deve ser realizado por grupos de 3 (ou 4) alunos.
Os detalhes da avaliação (datas para submissão do relatório e sua defesa
oral) são os que forem publicados na \cp{página da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo
em todos os exercícios do trabalho, para assim
poderem responder a qualquer questão colocada na
\emph{defesa oral} do relatório.

Em que consiste, então, o \emph{relatório} a que se refere o parágrafo anterior?
É a edição do texto que está a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relatório deverá conter ainda a identificação dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relatório deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o índice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2223t.aux
    $ makeindex cp2223t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou.

No anexo \ref{sec:codigo}, disponibiliza-se algum
código \Haskell\ relativo aos problemas apresentados. Esse anexo deverá
ser consultado e analisado à medida que isso for necessário.

\subsection{Como exprimir cálculos e diagramas em LaTeX/lhs2tex}
Como primeiro exemplo, estudar o texto fonte deste trabalho para obter o
efeito:\footnote{Exemplos tirados de \cite{Ol18}.}
\begin{eqnarray*}
\start
     |id = split f g|
%
\just\equiv{ universal property }
%
        |lcbr(
          p1 . id = f
     )(
          p2 . id = g
     )|
%
\just\equiv{ identity }
%
        |lcbr(
          p1 = f
     )(
          p2 = g
     )|
\qed
\end{eqnarray*}

Os diagramas podem ser produzidos recorrendo à \emph{package} \LaTeX\
\href{https://ctan.org/pkg/xymatrix}{xymatrix}, por exemplo:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Nat0|
           \ar[d]_-{|cataNat g|}
&
    |1 + Nat0|
           \ar[d]^{|id + (cataNat g)|}
           \ar[l]_-{|inNat|}
\\
     |B|
&
     |1 + B|
           \ar[l]^-{|g|}
}
\end{eqnarray*}

\section{Regra prática para a recursividade mútua em |Nat0|}\label{sec:mr}

Nesta disciplina estudou-se como fazer \pd{programação dinâmica} por cálculo,
recorrendo à lei de recursividade mútua.\footnote{Lei (\ref{eq:fokkinga})
em \cite{Ol18}, página \pageref{eq:fokkinga}.}

Para o caso de funções sobre os números naturais (|Nat0|, com functor
|fF X = 1 + X|) é fácil derivar-se da lei que foi estudada uma
  \emph{regra de algibeira}
  \label{pg:regra}
que se pode ensinar a programadores que não tenham estudado
\cp{Cálculo de Programas}. Apresenta-se de seguida essa regra, tomando como
exemplo o cálculo do ciclo-\textsf{for} que implementa a função de Fibonacci,
recordar o sistema:
\begin{spec}
fib 0 = 1
fib(n+1) = f n

f 0 = 1
f (n+1) = fib n + f n
\end{spec}
Obter-se-á de imediato
\begin{code}
fib' = p1 . for loop init where
   loop(fib,f)=(f,fib+f)
   init = (1,1)
\end{code}
usando as regras seguintes:
\begin{itemize}
\item O corpo do ciclo |loop| terá tantos argumentos quanto o número de funções
mutuamente recursivas.
\item Para as variáveis escolhem-se os próprios nomes das funções, pela ordem
que se achar conveniente.\footnote{Podem obviamente usar-se outros símbolos,
mas numa primeira leitura dá jeito usarem-se tais nomes.}
\item Para os resultados vão-se buscar as expressões respectivas, retirando
a variável |n|.
\item Em |init| coleccionam-se os resultados dos casos de base das funções,
pela mesma ordem.
\end{itemize}
Mais um exemplo, envolvendo polinómios do segundo grau $ax^2 + b x + c$ em |Nat0|.
Seguindo o método estudado nas aulas\footnote{Secção 3.17 de \cite{Ol18} e tópico
\href{https://www4.di.uminho.pt/~jno/media/cp/}{Recursividade mútua}
nos vídeos de apoio às aulas teóricas.},
de $f\ x = a x^2 + b x + c$ derivam-se duas funções mutuamente recursivas:
\begin{spec}
f 0 = c
f (n+1) = f n + k n

k 0 = a + b
k(n+1) = k n + 2 a
\end{spec}
Seguindo a regra acima, calcula-se de imediato a seguinte implementação, em Haskell:
\begin{code}
f' a b c = p1 . for loop init where
  loop(f,k) = (f+k,k+2*a)
  init = (c,a+b) 
\end{code}

\section{O mónade das distribuições probabilísticas} \label{sec:probabilities}
%format B = "\mathit B"
%format C = "\mathit C"
Mónades são functores com propriedades adicionais que nos permitem obter
efeitos especiais em progra\-mação. Por exemplo, a biblioteca \Probability\
oferece um mónade para abordar problemas de probabilidades. Nesta biblioteca,
o conceito de distribuição estatística é captado pelo tipo
\begin{eqnarray}
     |newtype Dist a = D {unD :: [(a, ProbRep)]}|
     \label{eq:Dist}
\end{eqnarray}
em que |ProbRep| é um real de |0| a |1|, equivalente a uma escala de $0$ a
$100 \%$.

Cada par |(a,p)| numa distribuição |d::Dist a| indica que a probabilidade
de |a| é |p|, devendo ser garantida a propriedade de  que todas as probabilidades
de |d| somam $100\%$.
Por exemplo, a seguinte distribuição de classificações por escalões de $A$ a $E$,
\[
\begin{array}{ll}
A & \rule{2mm}{3pt}\ 2\%\\
B & \rule{12mm}{3pt}\ 12\%\\
C & \rule{29mm}{3pt}\ 29\%\\
D & \rule{35mm}{3pt}\ 35\%\\
E & \rule{22mm}{3pt}\ 22\%\\
\end{array}
\]
será representada pela distribuição
\begin{code}
d1 :: Dist Char
d1 = D [('A',0.02),('B',0.12),('C',0.29),('D',0.35),('E',0.22)]
\end{code}
que o \GHCi\ mostrará assim:
\begin{Verbatim}[fontsize=\small]
'D'  35.0%
'C'  29.0%
'E'  22.0%
'B'  12.0%
'A'   2.0%
\end{Verbatim}
É possível definir geradores de distribuições, por exemplo distribuições \emph{uniformes},
\begin{code}
d2 = uniform (words "Uma frase de cinco palavras")
\end{code}
isto é
\begin{Verbatim}[fontsize=\small]
     "Uma"  20.0%
   "cinco"  20.0%
      "de"  20.0%
   "frase"  20.0%
"palavras"  20.0%
\end{Verbatim}
distribuição \emph{normais}, eg.\
\begin{code}
d3 = normal [10..20]
\end{code}
etc.\footnote{Para mais detalhes ver o código fonte de \Probability, que é uma adaptação da
biblioteca \PFP\ (``Probabilistic Functional Programming''). Para quem quiser saber mais
recomenda-se a leitura do artigo \cite{EK06}.}
|Dist| forma um \textbf{mónade} cuja unidade é |return a = D [(a,1)]| e cuja composição de Kleisli
é (simplificando a notação)
\begin{spec}
  ((kcomp f g)) a = [(y,q*p) | (x,p) <- g a, (y,q) <- f x]
\end{spec}
em que |g: A -> Dist B| e |f: B -> Dist C| são funções \textbf{monádicas} que representam
\emph{computações probabilísticas}.

Este mónade é adequado à resolução de problemas de \emph{probabilidades e estatística} usando programação funcional, de forma elegante e como caso particular da programação monádica.

\section{Código fornecido}\label{sec:codigo}

\subsection*{Problema 1}
Alguns testes para se validar a solução encontrada:
\begin{code}
test a b c = map (fbl a b c) x == map (f a b c) x where x = [1..20]  

test1 = test 1 2 3
test2 = test (-2) 1 5
\end{code}

\subsection*{Problema 2}

\textbf{Verificação}: a árvore de tipo \Exp\ gerada por
\begin{code}
acm_tree = tax acm_ccs
\end{code}
deverá verificar as propriedades seguintes:
\begin{itemize}
\item |expDepth acm_tree == 7| (profundidade da árvore);
\item |length (expOps acm_tree) == 432| (número de nós da árvore);
\item |length (expLeaves acm_tree) == 1682| (número de folhas da árvore).\footnote{Quer dizer, o número total de nodos e folhas é |2114|, o número de linhas do texto dado.}
\end{itemize}
O resultado final
\begin{code}
acm_xls  = post acm_tree
\end{code}
não deverá ter tamanho inferior ao total de nodos e folhas da árvore.

\subsection*{Problema 3}
Função para visualização em \svg:
\begin{code}
drawSq x = picd'' [ Svg.scale 0.44 (0,0) (x >>= sq2svg) ]
sq2svg (p,l) = (color "#67AB9F" . polyg) [ p, p .+ (0,l), p .+ (l,l), p .+ (l,0) ]
\end{code}
Para efeitos de temporização:
\begin{code}
await = threadDelay 1000000
\end{code}

\subsection*{Problema 4}
Rankings:
\begin{code}
rankings = [
         ("Argentina",4.8),
         ("Australia",4.0),
         ("Belgium",5.0),
         ("Brazil",5.0),
         ("Cameroon",4.0),
         ("Canada",4.0),
         ("Costa Rica",4.1),
         ("Croatia",4.4),
         ("Denmark",4.5),
         ("Ecuador",4.0),
         ("England",4.7),
         ("France",4.8),
         ("Germany",4.5),
         ("Ghana",3.8),
         ("Iran",4.2),
         ("Japan",4.2),
         ("Korea Republic",4.2),
         ("Mexico",4.5),
         ("Morocco",4.2),
         ("Netherlands",4.6),
         ("Poland",4.2),
         ("Portugal",4.6),
         ("Qatar",3.9),
         ("Saudi Arabia",3.9),
         ("Senegal",4.3),
         ("Serbia",4.2),
         ("Spain",4.7),
         ("Switzerland",4.4),
         ("Tunisia",4.1),
         ("USA",4.4),
         ("Uruguay",4.5),
         ("Wales",4.3)]
\end{code}
Geração dos jogos da fase de grupos:
\begin{code}
generateMatches = pairup
\end{code}
Preparação da árvore do ``mata-mata'':
\begin{code}
arrangement = (>>= swapTeams) . chunksOf 4 where
  swapTeams [[a1,a2],[b1,b2],[c1,c2],[d1,d2]] = [a1,b2,c1,d2,b1,a2,d1,c2]
\end{code}
Função proposta para se obter o \emph{ranking} de cada equipa:
\begin{code}
rank x = 4 ** (pap rankings x - 3.8)
\end{code}
Critério para a simulação não probabilística dos jogos da fase de grupos:
\begin{code}
gsCriteria = s . split (id >< id) (rank >< rank) where
  s ((s1, s2), (r1, r2)) = let d = r1 - r2 in
                           if d > 0.5 then Just s1
                                      else if d < -0.5 then Just s2
                                                       else Nothing
\end{code}
Critério para a simulação não probabilística dos jogos do mata-mata:
\begin{code}
koCriteria = s . split (id >< id) (rank >< rank) where
  s ((s1, s2), (r1, r2)) = let d = r1 - r2 in
                           if d == 0 then s1
                                     else if d > 0 then s1 else s2
\end{code}
Critério para a simulação probabilística dos jogos da fase de grupos:
\begin{code}
pgsCriteria = s . split (id >< id) (rank >< rank) where
  s ((s1, s2), (r1, r2)) =
     if abs(r1-r2) > 0.5 then fmap Just (pkoCriteria(s1,s2)) else f (s1,s2)
  f = D . ((Nothing,0.5):) . map (Just><(/2)) . unD . pkoCriteria
\end{code}
Critério para a simulação probabilística dos jogos do mata-mata:
\begin{code}
pkoCriteria (e1, e2) = D [(e1, 1 - r2 / (r1 + r2)), (e2, 1 - r1 / (r1 + r2))] where
    r1 = rank e1
    r2 = rank e2
\end{code}
Versão probabilística da simulação da fase de grupos:\footnote{Faz-se ``trimming'' das distribuições para reduzir o tempo de simulação.}
\begin{code}
psimulateGroupStage = trim .  map (pgroupWinners pgsCriteria)
trim = top 5 . sequence . map (filterP.norm)  where
   filterP (D x) = D [(a,p) | (a,p) <- x, p > 0.0001 ]
   top n = vec2Dist . take n . reverse . presort snd . unD 
   vec2Dist x = D [ (a,n/t) | (a,n) <- x ] where t = sum(map snd x) 
\end{code}
Versão mais eficiente da |pwinner| dada no texto principal, para diminuir o tempo de cada
simulação:
\begin{code}
pwinner :: Dist Team
pwinner = mbin f x >>= pknockoutStage where
   f(x,y) = initKnockoutStage(x++y)
   x = split (g . take 4) (g . drop 4) groups
   g = psimulateGroupStage . genGroupStageMatches
\end{code}
Auxiliares:
\begin{code}
best n = map fst . take n . reverse . presort p2

consolidate :: (Num d, Eq d, Eq b) => [(b, d)] -> [(b, d)]
consolidate = map (id><sum) . collect


collect :: (Eq a, Eq b) => [(a, b)] -> [(a, [b])]
collect x = nub [ k |-> [ d' | (k',d') <- x , k'==k ] | (k,d) <- x ]
\end{code}
Função binária monádica |f|:
\begin{code}
mmbin :: Monad m => ((a, b) -> m c) -> (m a, m b) -> m c
mmbin f (a,b) = do { x <- a ; y <- b ; f(x,y) }
\end{code}
Monadificação de uma função binária |f|:
\begin{code}
mbin :: Monad m => ((a, b) -> c) -> (m a, m b) -> m c
mbin = mmbin . (return.)
\end{code}
Outras funções que podem ser úteis:
\begin{code}
(f `is` v) x = (f x) == v

rcons(x,a) = x++[a]
\end{code}

%----------------- Soluções dos alunos -----------------------------------------%

\section{Soluções dos alunos}\label{sec:resolucao}
Os alunos devem colocar neste anexo as suas soluções para os exercícios
propostos, de acordo com o ``layout'' que se fornece. Não podem ser
alterados os nomes ou tipos das funções dadas, mas pode ser adicionado
texto, diagramas e/ou outras funções auxiliares que sejam necessárias.

Valoriza-se a escrita de \emph{pouco} código que corresponda a soluções
simples e elegantes.

\subsection*{Problema 1}
Funções auxiliares pedidas:


Para tornar fbl num \emph{for}, é  necessário primeiro definir algumas funções auxiliares, que nos permitam através das leis da recursividade mútua chegar a um catamorfismo, neste caso dos Números Naturais. Começamos por definir algumas funções iniciais (p, q e r), que se chamam recursivamente umas às outras, um dos princípios da recursividade mútua, e após continuarmos a desenvolver estes cálculos, conseguimos finalmente chegar a um Catamorfismo que pode ser transformado num \emph{for}, conseguindo assim descobrir a definição de \emph{loop} e \emph{initial}.

Consideremos F2:
\begin{eqnarray*}

	id + |split (split j k) l | = F |split (split j k) l|

	\start
    |lcbr(
          p a b c 0 = 1
    )(
          p a b c (n+1) = a * (p a b c n) + b * q a b c  n + c* r a b c n
    )|

    |lcbr(
          q a b c 0 = 1
    )(
          q a b c (n+1) = p n
     )|

    |lcbr(
          r a b c 0 = 0
    )(
          r a b c (n+1) = q n
     )|

\just\equiv{ Def-const (75) * 6; Def succ; Def (a*); Def (b*); Def (c*); Def-comp(73) * 8; Def-split(77)*2}
%
    |lcbr(
          ((p a b c) . 0) n = (const 1) n
    )(
          ((p a b c) >< succ) n  = add .( split (add . (split ((a*) . (p a b c)) ((b*) . (q a b c)))) ((c*) . (r a b c))) n
    )|

    |lcbr(
          ((q a b c) . 0) n = (const 1) n
    )(
          ((q a b c) . succ) n = p a b c n
     )|

    |lcbr(
          ((r a b c) . 0) n = (const 0) n
    )(
          ((r a b c ) . succ) n = q a b c n
     )|
\just\equiv{ Igualdade estensional (72) * 6; Absorção-x (11) * 2}
%
    |lcbr(
          (p a b c) . (const 0) = (const 1)
    )(
          (p a b c) >< succ  = add .(add . ((a*) >< (b*)) >< (c*)) . split (split (p a b c) (q a b c)) (r a b c)
    )|

    |lcbr(
          (q a b c) . (const 0) = (const 1)
    )(
          (q a b c) . succ = p a b c
     )|

    |lcbr(
          (r a b c) . (const 0) = (const 0)
    )(
          (r a b c ) . succ = q a b c
     )|

\just\equiv{Def in; Cancelamento-+ (18) * 6; p a b c = j; q a b c = k; r a b c = l}
%
    |lcbr(
          j . in . i1 = (const 1)
    )(
          j . in . i2  = add .(add . ((a*) >< (b*)) >< (c*)) . split (split j k) l
    )|

    |lcbr(
          k . in . i1 = (const 1)
    )(
          k . in . i2  = j
     )|

    |lcbr(
          l . in . i1 = (const 0)
    )(
          l . in . i2 = k
     )|
\just\equiv{Cancelamento-+ (18) * 3}
    |lcbr3(
          j . in = either (const 1) ( add .(add . ((a*) >< (b*)) >< (c*)) . split (split j k) l)
    )(
          k . in = either (const 1) j
    )(
          l . in= either (const 0) k
    )|

\just\equiv{Natural-id(1); Absorção-x(22); Cancelamento-x(7) * 4}
    |lcbr3(
          j . in = either (const 1) ( add .(add . ((a*) >< (b*)) >< (c*))) . (1 + split (split j k) l)
    )(
          k . in = either (const 1) (p1.p1. split (split j k)(l))
    )(
          l . in= either (const 0) (p2.p1.split (split j k)(l))
    )|
\just\equiv{Natural-id(1)*2; Absorção-x(22) * 2;F2}
    |lcbr(
          j . in = either (const 1) ( add .(add . ((a*) >< (b*)) >< (c*))) . (1 + split (split j k) l)
    )(
          k . in = (either (const 1) (p1.p1) ) . F (split (split j k) l)
    )(
          l . in = (either (const 0) (p2.p1). F (split (split j k)(l)))
    )|
\just\equiv{Eq-x(16); Fusão-x(9) * 2}
    |lcbr(
          split j k . in = (split (either (const 1) (add.(add.((a*)><(b*))><(c*))) ) (either (const 1) (p1.p1))) . F (split (split j k) l)
    )(
          l . in = (either (const 1) (p2.p1) ) . F (split (split j k) l)
    )|
\just\equiv{Lei da Troca(28)}
    |lcbr(
          split j k . in = (either (split (const 1) (const 1)) (split (add.(add.((a*)><(b*))><(c*))) (p1.p1))) . F (split (split j k) l)
    )(
          l . in = (either (const 1) (p2.p1) ) . F (split (split j k) l)
    )|
\just\equiv{Fokkinga(53)}
    |split (split j k) l = cata( either (split (split (const 1) (const 1)) (const 0)) (split (split (add.(add.((a*)><(b*))><(c*))) (p1.p1)) (p2.p1)) ) |
\just\equiv{j = p a b c; k = q a b c; l = r a b c}
    |split (split (p a b c) (q a b c)) (r a b c) = cata( either (split (split (const 1) (const 1)) (const 0)) (split (split (add.(add.((a*)><(b*))><(c*))) (p1.p1)) (p2.p1)) )   |
\qed

    |split (split (const 1)(const 1)) (const 0) = (const (((1,1),0))|
\just\eqiv{ Igualdade estensional (72); Def-split(77)*2; Def-const (75) * 4}
    |((1,1),0) = ((1,1),0)|



\qed
\end{eqnarray*}
\begin{code}

loop a b c = split (split (add . ((add . ((a*) >< (b*))) >< (c*))) (p1 . p1)) (p2 . p1)
initial = ((1,1),0) 
wrap = p2

\end{code}

\textbf{Testes de Performance}

Apresenta-se agora duas imagens (figuras \ref{fig:testeF} e \ref{fig:testeFbl}) que demonstram o quão mais eficiente fbl é em relação a f.

\begin{figure}[h!]
  \centering
  \includegraphics[width=0.9\textwidth]{cp2223t_media/teste.png}
  \caption{Execução de f 1 1 1 para diferentes tamanhos de input}
  \label{fig:testeF}
\end{figure}

\begin{figure}[h!]
  \centering
  \includegraphics[width=0.9\textwidth]{cp2223t_media/testefibl.png}
  \caption{Execução de fbl 1 1 1 para diferentes tamanhos de input}
  \label{fig:testeFbl}
\end{figure}

É possível ver que para f (figura \ref{fig:testeF}), à medida que o tamanho do input vai aumentando, o tempo de execução vai aumentando também, mas de forma exponencial, enquanto para fbl (figura \ref{fig:testeFbl}) o tempo de execução se mantém igual (não mostramos mais porque já deu para verificar que é muito mais eficiente).

\subsection*{Problema 2}

Neste exercício é pedido que apresentemos uma definição para o gene do anaformismo do tipo \emph{Exp S S}, a partir de uma lista de String. Olhando para a definição de um anaformismo para este tipo de dados, vimos que o seu Functor aplica a um id lado esquerdo do + (ou seja, a tudo que apareça do tipo i1 a, é lhe aplicado um id), e do lado direito aplica um id ao lado esquerdo da multiplicação e faz um map com o anamorfismo que estejamos a definir do lado direito, pelo que na nossa definição de gene, decidimos tirar partido de out, que no caso de uma lista ser singular (só um elemento), devolve i1 com esse elemento, caso contrário coloca o primeiro elemento na primeira posição de um par, e o resto na segunda, aplicando ao resultado dessa função uma soma de funções, que a algo do tipo i1 lhe faz id, e se for um par separa a lista (lado direito) pelas diferentes sub-árvores com um nível de indentação acima do elemento da cabeça (primeiro elemento do par).

Gene de |tax|:
\begin{code}
gene = (id -|- separa) . out

separa (a,b) = (a, (groupBy (\_ y -> nivelIdent y > identPai) b))
   where identPai = 1+nivelIdent a

nivelIdent l = div (contaEspacos l) 4

contaEspacos [] = 0
contaEspacos (h:t) = if (h /= ' ') then 0 else 1 + contaEspacos t

\end{code}
\begin{eqnarray*}
\xymatrix@@C=7cm{
    |S|^*
      \ar[d]^{|tax|}
      \ar[r]^{|gene|}
&
    |S|^* + |S|^* \times (S^*)^*
           \ar[d]^{|id + id >< maptax|}
\\
     | Exp S S|
&
    |S|^* + |S|^*|>< Exp S S|
           \ar[l]^{|inExp|}
}
\end{eqnarray*}

Nesta segunda parte do exercício, é pedido para definir a função post, que recebe uma Exp S S e retorna uma lista de lista de String, em que cada uma dessas listas corresponderá a um caminho na árvore. Para a definir acabamos por definir duas funções auxiliares, uma que coloca um elemento numa lista de listas (aplicado a elementos da árvore do tipo Var), e outra que recebendo um par (elemento,lista de listas), coloca esse elemento na cabeça de todas as listas que estejam na lista que está do lado direito do par. Assim, resumidamente, esta função começa a desconstruir a árvore Exp S S pelas folhas, e começa a construir o resultado final através da adição das diferentes String de nível abaixo (considerando que um nível maior corresponde a maior indentação) à cabeça das folhas, criando os caminhos iterativamente, até que se chegue ao pai, tendo assim o resultado final.

Função de pós-processamento:
\begin{code}

post = (either (doubleSingl) (cons . (split (p1) (fstACabeca) . (singleton >< (concatMap (post))) ))) . outExp
    where doubleSingl = singleton . singleton
          fstACabeca (x,l) = map (x++) l 
          

\end{code}

\subsection*{Problema 3}

Neste exercício foi nos pedido para fazer um anamorfismo de Rose Tree Square, ou seja, uma Rose Tree em que a informação contida na mesma são os quadrados correspondentes aos diferentes níveis do tapete de sierpinski.

À semelhança do exercício anterior onde fizemos um anamorfismo, começamos por averiguar o funcionamento de anaRose, anamorfismo de Rose Tree's, e verificamos que neste caso o Functor é aplicado a um par, em que ao elemento do lado esquerdo é aplicada a identidade, e do lado direito é feito um  map com o próprio anamorfismo, pelo que o gene deste anamorfismo teria que transformar o input dado em algo compatível com esse tipo. 

O que nós fizemos foi uma função que, ao receber um quadrado e uma profundidade, se essa profundidade for 0, retornamos um par em que do lado esquerdo termos o quadrado que se localiza no meio do que é dado como argumento, e do lado direito uma lista vazia. Caso essa profundidade não seja 0, o comportamento para o lado esquerdo é idêntico ao explicado para caso a profundidade seja 0, mas do lado direito é retornada uma lista com os sub quadrados onde os próximos elementos da sequência devem ser desenhados, com profundidade decrementada.

\begin{code}
squares = anaRose gsq

gsq (((x,y),s),0) = ( ((x+(s/3),y+(s/3)),s/3) ,[])
gsq (sq@((x,y),s),p+1) = (((x+newSide,y+newSide),newSide) , filhosFinal)
    where newSide = s/3
          filhos = coordsFilhos sq
          filhosFinal = map (addDir p) filhos

coordsFilhos ((x,y),side) = [ ((x+xO, y+yO),nS)|xO<-offsets,yO<-offsets,(xO/=yO||x/=nS) ]
    where nS = side/3
          offsets = [0, nS, 2*nS]
addDir v p = (p,v)

\end{code}
\begin{eqnarray*}
\xymatrix@@C=3cm{
    Square \times Integer
           \ar[d]^{|squares|}
           \ar[r]^{|gsp|}
&
    Square \times (Square \times Integer)^*
           \ar[d]^{id \times map squares}
\\
     |Rose Square|
&
     Square  \times (Rose Square)^*
           \ar[l]^{|inRose|}
}
\end{eqnarray*}

Em seguida, ainda na primeira parte do Exercício 3, é pedido um catamorfismo usado para converter uma Rose Tree em uma lista.

Considerando que uma Rose Tree é constituída por um elemento e uma lista de Rose Tree, apenas aplicamos a identidade a esse elemento que ficará na cabeça, e concatenamos a lista de Rose Tree (que quando é concatenada ja foi transformada numa lista de listas de elementos).

\begin{code}


rose2List = cataRose gr2l 

gr2l = cons . (id >< concat)

\end{code}
\begin{center}
\begin{eqnarray*}
\xymatrix@@C=4cm{
    |Rose A|
           \ar[d]^{|rose2List|}
           \ar[r]^{|outRose|}
&
    A \times (Rose A)^*
           \ar[d]^{id \times  rose2List}
\\
     |[A]|
&
      A  \times (A^*)^*
           \ar[l]^{|gr2l|}
}
\end{eqnarray*}
\end{center}

Já na segunda parte do exercício, foi nos pedido para definir, numa primeira parte, um anamorfismo, que construirá, recebendo um inteiro n, a lista com os tapetes de profundidade 1 até n.

No gene deste anamorfismo começamos por primeiro aplicar o outNat, para poder transformar em algo que o anamorfismo pudesse usar. Ao resultado dessa função aplicamos uma soma de funções, que a algo do tipo i1 () aplica a identidade, e a algo do tipo i2 a, aplicámos um split que cria um par que do lado esquerdo terá uma lista de Square (um tapete) e do lado direito terá a profundidade do próximo tapete a gerar.

\begin{code}

sqInicial = split (const ((0,0),32)) id

carpets = anaList geneCarpets

geneCarpets = ((id -|- (split (sierpinski . sqInicial) id)) . outNat)

\end{code}
\begin{center}
\begin{eqnarray*}
\xymatrix@@C=7cm{
    |Nat0|
           \ar[d]^{|carpets|}
           \ar[r]^{|genecarperts|}
&
    1 + Square^* \times |Nat0|
           \ar[d]^{id + id \times carpets}
\\
     (Square^*)^*
&
      1 + Square^*  \times (Square^*)^*
           \ar[l]^{|inList|}
}
\end{eqnarray*}
\end{center}

Em seguida foi pedido para definir um catamorfismo que percorre uma lista de listas de Square, desenhando todos os elementos, com 1 segundo de intervalo entre os mesmos.

Este exercício foi complicado pois adiciona uma componente monádica, sendo preciso termos em conta isso para o retorno da função. No gene do catamorfismo, se for recebido algo do tipo i1 () apenas retornamos uma lista vazia, e caso tenhamos algo do tipo i2 (a,b), aplicamos a função consIO que, recebendo um par ([Square], IO [()]), retorna apenas IO [()], e que, antes de fazer essa junção, desenha o tapete e espera 1 segundo. 

É de reforçar que antes de correr o catamorfismo aplicamos um reverse à lista dada como input, visto que a lista retornada por carpets tem primeiro os tapetes de profundidade mais elevada, e nós aqui queremos desenhar primeiro os de profundidade mais baixa. Possivelmente esta não é a melhor alternativa, mas foi a única maneira que (até agora) arranjamos de resolver este problema.


\begin{code}

ignora1 a = return []

apresentaSq :: [Square] -> IO ()
apresentaSq a = drawSq a >> await >>= return

consIO (h,t) = do { r1 <- apresentaSq h ; r2 <- t ; return (r2 ++ [r1]) }

genePresent :: Either () ([Square], IO [()]) -> IO [()]
genePresent = either (ignora1) (consIO)

present :: [[Square]] -> IO [()]
present = cataList genePresent . reverse
\end{code}

\subsection*{Problema 4}

Antes de partir para a resolução do exercício em si, queríamos apenas clarificar que apenas resolvemos a parte não probabilística deste exercício. 

\subsubsection*{Versão não probabilística}

Na primeira parte desta versão do exercício, é nos proposta a definição de cgene, o gene do catamorfismo consolidate', que é usado para calcular os pontos de cada equipa no final da simulação da fase de grupos.

Para a resolução desse problema definimos uma função auxiliar que recebe um par ((equipa, pontos), [(equipa, pontos)]), e que devolve [(equipa, pontos)], que soma todos os pontos que a equipa passa no primeiro par do argumento tem.

No próprio gene do catamorfismo, apenas aplicamos um either em que, algo do tipo i1 () é transformado numa lista vazia, a algo do tipo i2 a é aplicada a função explicada acima.

Gene de |consolidate'|:
\begin{code}
cgene :: (Eq a, Num b) => Either () ((a,b), [(a,b)]) -> [(a,b)]
cgene = (either nil adiciona)

adiciona (p,[]) = singleton p
adiciona ((a,b), (a1,b1):t) = if a==a1 then (a,b + b1):t else (a1,b1) : adiciona ((a,b),t)
\end{code}
%--adiciona ((a,b),(a1,b1):t) = (Cp.cond (a==) ((a,b+b1):t) (cons ((a1,b1) , (adiciona ((a,b),t))) ) ) a1

\begin{eqnarray*}
\xymatrix@@C=7cm{
    |(A><B)|^*
      \ar[d]^{|consolidate'|}
      \ar[r]^{|outList|}
&
    |1 + (A><B) >< (A><B)|^*
           \ar[d]^{|id + id >< consolidate'|}
\\
    |A><B|^*
&
    |1 + (A><B) >< (A><B)|^*
           \ar[l]^{|cgene|}
}
\end{eqnarray*}

Em seguida é nos solicitado que apresentemos uma definição para a função pairup que, recebendo uma lista de equipas, retorna uma lista com todos os jogos que devem ser realizados entre essas equipas.

Depois pedem ainda que seja definida uma função que retorna uma lista com os pontos associados a duas equipas que realizam um jogo entre si, e ainda um gene para o anamorfismo que é usado para transformar a lista dos vencedores da fase de grupos em uma LTree de equipas, referente à fase eliminatória do campeonato.

Vamos agora explicar brevemente como pensamos para resolver cada um dos requisitos:

\begin{itemize}

	\item pairup: recebe uma lista de equipas e adiciona à lista final todos os jogos que a equipa a cabeça pode fazer com o resto das equipas, chamando-se a si própria recursivamente para o resto das equipas.

	\item matchResult: aplicamos a função de critério ao jogo em questão, sabendo que o resultado disso é Maybe Team, definimos um outMaybe, que recebendo um Maybe a retorna i1 () caso seja Nothing e i2 a caso seja Just a, aplicando em seguida um either que retorna a lista correspondente aos pontos de cada equipa.

	\item glt: sendo este o gene de um anamorfismo de LTree A, tendo neste caso que A é do tipo Team. Definimos uma função auxiliar chamada outTeamList que, recebendo uma lista de equipas, se esta só tiver um elemento, retorna i1 a, sendo a esse elemento, e caso contenha mais que um elemento retorna i2 (a,b), em que a e b são duas metades da lista.

\end{itemize}

Geração dos jogos da fase de grupos:
\begin{code}
pairup [] = []
pairup (x:xs) = map (split (const x) id) xs ++ pairup xs

outMaybe Nothing = i1 ()
outMaybe (Just a) = i2 a

empate (a,b) _ = [(a,1),(b,1)]

vencedor (a,b) v = [(vencedor,3),(derrotado,0)]
    where (vencedor,derrotado) = if a==v then (a,b) else (b,a)

matchResult func jogo = ((either (empate jogo) (vencedor jogo)) . outMaybe . func) jogo 

outTeamList [t] = i1 t
outTeamList l = let splitPoint = div (length l) 2
                    sl = splitAt splitPoint l
                in i2 sl

glt = outTeamList

\end{code}
\begin{eqnarray*}
\xymatrix@@C=5cm{
    |A|^*
      \ar[d]^{|ana(g)|}
      \ar[r]^{|glt|}
&
    |A + A|^*|>< A|^*
           \ar[d]^{|id + ana(glt) >< ana(glt)|}
\\
    LTree A
&
    |A + LTree A >< LTree A |
           \ar[l]^{|inLTree|}
}

\end{eqnarray*}
\subsubsection*{Versão probabilística}

Como já referimos, acabamos por não fazer esta parte do trabalho, apenas definimos a função pmatchResult, que recebendo o critério e um jogo nos dá um Dist ([(Team,Int)]), com a probabilidade dos pontos das equipas no final do jogo serem esses.

\begin{code}
pinitKnockoutStage = undefined

getMatch (D l) = ((split (head) (head . tail)) . (map fst) . fst . head) l 

sameMatch (a,b) (a1,b1) = (a == b && a1 == b1) || (a==b1 && b == a1) 

\end{code}
%--% padiciona (p,[]) singleton = singleton p
%--% padiciona ((p1@(a,b),prob), (p2@(a1,b1),prob2):t)
%--%  | p1 == p2 = (p2,prob2) : padiciona ((p1,prob1):t)
\begin{code}

pgroupWinners :: (Match -> Dist (Maybe Team)) -> [Match] -> Dist [Team]
pgroupWinners pcriteria = undefined  

pmatchResult func match = fmap (either (empate match) (vencedor match) . outMaybe) (func match)
\end{code}

%----------------- Índice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2223t}

%----------------- Fim do documento -------------------------------------------%

\end{document}
