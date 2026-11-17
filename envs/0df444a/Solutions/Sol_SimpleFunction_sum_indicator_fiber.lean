-- Prove2me | solution 1 for SimpleFunction.sum_indicator_fiber
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:44:30.664657+00:00
-- url     : https://prove2.me/submissions/007d224c-9ff4-4f1a-9282-c6c4a69c4869

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_1_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic


/-

  # Simple function

-/

/-
\begin{defbox}{6.1}
Let $(\Omega,\mathcal{F},\mu)$ be a measure space. A function $X:\Omega \to \bar{\mathbb{R}}$ is called a \textit{simple function} if its range is finite and it is $\mathcal{F}$-measurable.

Suppose $X$ takes on $n$ distinct values, denoted by $a_1,a_2,\ldots,a_n$, for some integer $n$. Since $X$ is a function with values in $\bar{\mathbb{R}}$, one of the $a_i$'s may be $\infty$ or $-\infty$. For $i=1,2,\ldots,n$, let $A_i$ be the pre-image $X^{-1}(\{a_i\}) \triangleq \{\omega : X(\omega)=a_i\}$. Because a simple function is $\mathcal{F}$-measurable by definition, the sets $A_i$'s are also $\mathcal{F}$-measurable and form a partition of the sample space $\Omega$. We can write $X(\omega)$ as a linear combination of indicator functions
\begin{equation}
X(\omega)=\sum_{i=1}^{n} a_i 1_{A_i}(\omega).
\tag{6.1}
\end{equation}
\end{defbox}
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators

section SimpleFunction
open SimpleFunction

variable {Ω : Type*} [MeasurableSpace Ω]


theorem solution (X : SimpleFunction Ω) :
    X = fun ω => ∑ x ∈ X.range, Set.indicator (X ⁻¹' ({x} : Set EReal)) (fun _ => x) ω := by
  classical
  funext ω
  rw [Finset.sum_eq_single (X ω)]
  · simp [Set.indicator_of_mem]
  · intro y hy hy_ne
    have hω : ω ∉ X ⁻¹' ({y} : Set EReal) := by
      intro h_mem
      exact hy_ne ((by simpa using h_mem) : X ω = y).symm
    simp [Set.indicator_of_notMem, hω]
  · intro h_not_mem
    exact (h_not_mem (X.mem_range_self ω)).elim
end SimpleFunction
