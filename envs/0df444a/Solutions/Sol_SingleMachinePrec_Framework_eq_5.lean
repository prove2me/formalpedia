-- Prove2me | solution 1 for SingleMachinePrec.Framework.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:49:21.277197+00:00
-- url     : https://prove2.me/submissions/060a9a17-f5ce-4d8a-b6dc-7cee9526c02f

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_CSLP

set_option autoImplicit false

open SingleMachinePrec.Framework in
theorem solution {N : Type*} [Fintype N] (S : Instance N) (k t : ℕ)
    (L : Fin t → LinearExtension S.P) (hL : IsKFoldRealizer S.P k t L)
    (x : IncPair S.P → ℝ) :
    ((k : ℝ) / t) * weight S (levelSet x (1 / 2)) ≤
      (1 / (t : ℝ)) * ∑ i, weight S (reversedHalf x (L i)) := by
  classical
  obtain ⟨ht, hk⟩ := hL
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have key : (k : ℝ) * weight S (levelSet x (1 / 2)) ≤
      ∑ i, weight S (reversedHalf x (L i)) := by
    unfold weight reversedHalf
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u _
    have hw : 0 ≤ vertexWeight S u := mul_nonneg (S.p_nonneg _) (S.w_nonneg _)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk u) hw
  rw [div_mul_eq_mul_div, one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right key htpos.le
