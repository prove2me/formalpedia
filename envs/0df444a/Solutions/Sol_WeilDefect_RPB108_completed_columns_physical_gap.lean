-- Prove2me | solution 1 for WeilDefect.RPB108.completed_columns_physical_gap
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T20:17:37.199488+00:00
-- url     : https://prove2.me/submissions/58cf5ae4-4284-427c-afe5-5ef4a077876c

import Theorems.Thm_WeilDefect_RPB108_four_column_tail_gap
import Theorems.Thm_WeilDefect_RPB108_completed_columns_norm_bound
import Mathlib
open scoped BigOperators
set_option autoImplicit false
open WeilDefect.RPB108
theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : Fin 4 → E) (b L : Fin 4 → ℝ) (k gap : ℝ)
    (hv : ∀ i, ‖v i‖ ≤ b i) (hL : ∀ i, 0 < L i) (hk : 0 < k)
    (hgap : 0 ≤ gap)
    (hbound : gap * ((∑ i, (b i)^2/L i) + 1/k) ≤ 1)
    (z : Fin 4 → ℂ) (h : E) (energy : ℝ)
    (henergy : (∑ i, L i * ‖z i‖^2) + k*‖h‖^2 ≤ energy) :
    gap * ‖(∑ i, z i • v i) + h‖^2 ≤ energy := by
  have hu := completed_columns_norm_bound v b hv z h
  have hs : ‖(∑ i, z i • v i) + h‖^2 ≤ ((∑ i, b i * ‖z i‖) + ‖h‖)^2 := by
    have hn := norm_nonneg ((∑ i, z i • v i) + h)
    nlinarith
  have hc := four_column_tail_gap b L k gap hL hk hgap hbound
    (fun i => ‖z i‖) ‖h‖ (norm_nonneg _)
  simp only [abs_of_nonneg (norm_nonneg _)] at hc
  exact ((mul_le_mul_of_nonneg_left hs hgap).trans hc).trans henergy
