-- Prove2me | solution 1 for ProjSelfConcordant.ConicExt.pmu_inv_kappa_nonneg_iff
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:08:24.06318+00:00
-- url     : https://prove2.me/submissions/2601830a-7dea-4bfd-bba8-6652311176c4

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting
import Theorems.Thm_ProjSelfConcordant_ConicExt_pmu_at_inv_kappa

namespace ProjSelfConcordant.ConicExt.EndpointProof

lemma products_iff (A B μ : ℝ) (hB : 0 ≤ B) (hBA : B ≤ A) :
    (0 ≤ (A + μ) * (B - μ) ∧ 0 ≤ (A - μ) * (B + μ)) ↔ |μ| ≤ B := by
  rw [abs_le]
  constructor
  · intro h
    constructor
    · by_contra hm
      have hleft : 0 < A - μ := by linarith
      have hright : B + μ < 0 := by linarith
      have := mul_neg_of_pos_of_neg hleft hright
      linarith [h.2]
    · by_contra hm
      have hleft : 0 < A + μ := by linarith
      have hright : B - μ < 0 := by linarith
      have := mul_neg_of_pos_of_neg hleft hright
      linarith [h.1]
  · rintro ⟨hlo, hhi⟩
    exact ⟨mul_nonneg (by linarith) (by linarith),
      mul_nonneg (by linarith) (by linarith)⟩

lemma coefficient_bounds (κ : ℝ) (hκ : 1 ≤ κ) :
    0 ≤ 2 * (κ ^ 2 - 1) / κ ∧
    2 * (κ ^ 2 - 1) / κ ≤ 2 * (κ ^ 4 + 5 * κ ^ 2 + 2) / κ ^ 3 := by
  have hk : 0 < κ := by linarith
  have hk2 : 0 ≤ κ ^ 2 - 1 := by nlinarith
  refine ⟨div_nonneg (mul_nonneg (by norm_num) hk2) hk.le, ?_⟩
  have hid : 2 * (κ ^ 4 + 5 * κ ^ 2 + 2) / κ ^ 3 - 2 * (κ ^ 2 - 1) / κ =
      12 / κ + 4 / κ ^ 3 := by
    field_simp
    <;> ring
  have hpos : 0 ≤ 12 / κ + 4 / κ ^ 3 := by positivity
  linarith

lemma bound_sqrt (κ : ℝ) (hκ : 1 ≤ κ) :
    2 * (κ ^ 2 - 1) / κ =
      2 * (((κ ^ 2 + 1) - 2) / Real.sqrt ((κ ^ 2 + 1) - 1)) := by
  have hκ0 : 0 ≤ κ := by linarith
  rw [add_sub_cancel_right, Real.sqrt_sq hκ0]
  ring

end ProjSelfConcordant.ConicExt.EndpointProof

open ProjSelfConcordant.ConicExt

theorem solution (κ μ : ℝ) (hκ : 1 ≤ κ) :
    ((0 ≤ pmu (κ ^ 2 + 1) μ (-κ⁻¹) ∧ 0 ≤ pmu (κ ^ 2 + 1) μ κ⁻¹) ↔ |μ| ≤ 2 * (κ ^ 2 - 1) / κ) ∧
      2 * (κ ^ 2 - 1) / κ = 2 * (((κ ^ 2 + 1) - 2) / Real.sqrt ((κ ^ 2 + 1) - 1)) := by
  obtain ⟨hminus, hplus⟩ := pmu_at_inv_kappa κ μ hκ
  obtain ⟨hB, hBA⟩ := EndpointProof.coefficient_bounds κ hκ
  refine ⟨?_, EndpointProof.bound_sqrt κ hκ⟩
  rw [hminus, hplus]
  exact EndpointProof.products_iff _ _ μ hB hBA
