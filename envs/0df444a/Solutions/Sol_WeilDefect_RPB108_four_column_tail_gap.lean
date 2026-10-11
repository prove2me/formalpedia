-- Prove2me | solution 1 for WeilDefect.RPB108.four_column_tail_gap
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T20:17:18.684754+00:00
-- url     : https://prove2.me/submissions/79b668ca-4c39-4d31-bf23-974cbf6bd1ab

import Theorems.Thm_WeilDefect_RPB108_physical_gap_of_denominator_bound
import Mathlib
open scoped BigOperators
set_option autoImplicit false
open WeilDefect.RPB108
theorem solution (w L : Fin 4 → ℝ) (k gap : ℝ)
    (hL : ∀ i, 0 < L i) (hk : 0 < k) (hgap : 0 ≤ gap)
    (hbound : gap * ((∑ i, (w i)^2 / L i) + 1/k) ≤ 1)
    (z : Fin 4 → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    gap * ((∑ i, w i * |z i|) + r)^2 ≤
      (∑ i, L i * (z i)^2) + k*r^2 := by
  let w' : Option (Fin 4) → ℝ := fun i => i.elim 1 w
  let L' : Option (Fin 4) → ℝ := fun i => i.elim k L
  let z' : Option (Fin 4) → ℝ := fun i => i.elim r z
  have hL' : ∀ i ∈ (Finset.univ : Finset (Option (Fin 4))), 0 < L' i := by
    intro i _
    cases i with
    | none => exact hk
    | some i => exact hL i
  have hb : gap * (∑ i ∈ (Finset.univ : Finset (Option (Fin 4))), (w' i)^2/L' i) ≤ 1 := by
    simpa [w', L', Fintype.sum_option, add_comm] using hbound
  have h := physical_gap_of_denominator_bound Finset.univ w' L' hL' gap hgap hb z'
  simpa [w', L', z', Fintype.sum_option, abs_of_nonneg hr, add_comm] using h
