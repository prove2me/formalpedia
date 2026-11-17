-- Prove2me | solution 1 for abs_eq_positivePart_add_negativePart
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:21:57.512907+00:00
-- url     : https://prove2.me/submissions/1d9e901a-c28a-4549-ab36-d6ce91e4e427

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_4_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic


/-
  # Definition 6.4 Positive part and negative part of real-valued function
-/

/-
\begin{defbox}{6.4}
For real-valued measurable function $X$, we let
\[
X^+ \triangleq \max(X,0)
\qquad \text{and} \qquad
X^- \triangleq -\min(X,0)
\]
be the \textit{positive part} and \textit{negative part} of $X$, respectively.

Both the positive and negative parts of $X$ are measurable because the functions $\max(x,0)$ and $-\min(x,0)$ are continuous (Theorem 4.5). Moreover, we have
\[
X=X^+-X^-
\qquad \text{and} \qquad
|X|=X^+ + X^-.
\]

Using these concepts, we can define the Lebesgue integral of a real-valued function by reducing the definition to the nonnegative case.
\end{defbox}
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

section PositiveNegativeParts

variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}


theorem solution (X : Ω → ℝ) :
    (fun ω => |X ω|) = fun ω => positivePart X ω + negativePart X ω := by
  funext ω
  by_cases hω : 0 ≤ X ω
  · have hneg : ¬ X ω < 0 := not_lt_of_ge hω
    have hmax : max (X ω) 0 = X ω := max_eq_left hω
    have hmin : min (X ω) 0 = 0 := min_eq_right hω
    have habs : |X ω| = X ω := abs_of_nonneg hω
    simp [positivePart, negativePart, hmax, hmin, habs]
  · have hlt : X ω < 0 := lt_of_not_ge hω
    have hmax : max (X ω) 0 = 0 := max_eq_right (le_of_lt hlt)
    have hmin : min (X ω) 0 = X ω := min_eq_left (le_of_lt hlt)
    have habs : |X ω| = -X ω := abs_of_neg hlt
    simp [positivePart, negativePart, hmax, hmin, habs]
end PositiveNegativeParts
