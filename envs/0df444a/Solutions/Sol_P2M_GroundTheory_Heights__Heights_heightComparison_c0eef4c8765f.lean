-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_heightComparison_c0eef4c8765f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:11:30.076882+00:00
-- url     : https://prove2.me/submissions/2a572a8a-dd2b-4cfe-ab70-8c00f636d609

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_bound_metricDefect_474cdf5ff6c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockSum_nonneg_b0b5b7ed1f1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coordVec_ne_zero_81a696e5203c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockNonzero_sigma_8db15361a0fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_eq_blockSum_d5c0c59058d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_standard_eq_blockSum_e27d47607e91

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : HeightComparison.Statement := by
  intro ι _ _ n P A
  obtain ⟨M, hM⟩ := exists_bound_metricDefect A
  refine ⟨∑ k, (A.deg k).natAbs, M, fun x hx ↦ ?_⟩
  have hxb : BlockNonzero x := hx.1
  have hd : (0 : ℝ) < Module.finrank ℚ (coordField x) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := coordField x)
  have hnn : ∀ k, 0 ≤ blockSum (coordVec x) k :=
    fun k ↦ blockSum_nonneg _ k (coordVec_ne_zero hxb k)
  rw [height_eq_blockSum A x hxb, height_standard_eq_blockSum x hxb]
  set d : ℝ := (Module.finrank ℚ (coordField x) : ℝ)
  set N : ℝ := ((∑ k, (A.deg k).natAbs : ℕ) : ℝ)
  have hR : |∑ σ : coordField x →+* ℂ, metricDefect A (fun k i ↦ σ (coordVec x k i))| ≤ d * M := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ M fun σ _ ↦ hM _ (blockNonzero_sigma hxb σ)).trans ?_
    rw [Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]
  have hak : ∀ k, |(A.deg k : ℝ)| ≤ N := by
    intro k
    have e : |(A.deg k : ℝ)| = ((A.deg k).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [e]
    simp only [N, Nat.cast_sum]
    exact Finset.single_le_sum (f := fun j ↦ ((A.deg j).natAbs : ℝ))
      (fun j _ ↦ Nat.cast_nonneg _) (Finset.mem_univ k)
  have hS : |∑ k, (A.deg k : ℝ) * blockSum (coordVec x) k| ≤ N * ∑ k, blockSum (coordVec x) k := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    rw [abs_mul, abs_of_nonneg (hnn k)]
    exact mul_le_mul_of_nonneg_right (hak k) (hnn k)
  rw [abs_mul, abs_of_pos (inv_pos.mpr hd)]
  have hsum := (abs_add_le _ _).trans (add_le_add hS hR)
  calc d⁻¹ * |∑ k, (A.deg k : ℝ) * blockSum (coordVec x) k +
        ∑ σ : coordField x →+* ℂ, metricDefect A (fun k i ↦ σ (coordVec x k i))|
      ≤ d⁻¹ * (N * ∑ k, blockSum (coordVec x) k + d * M) :=
        mul_le_mul_of_nonneg_left hsum (inv_pos.mpr hd).le
    _ = N * (d⁻¹ * ∑ k, blockSum (coordVec x) k) + M := by
        field_simp
end GroundTheory.Heights₂.Heights
