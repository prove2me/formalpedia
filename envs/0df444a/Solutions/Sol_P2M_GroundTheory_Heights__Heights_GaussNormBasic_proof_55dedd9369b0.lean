-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussNormBasic_proof_55dedd9369b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:57:05.36381+00:00
-- url     : https://prove2.me/submissions/2c39683f-f91b-4754-8094-ef3fd8ea9c71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_isNonarchimedean_normAbv_86b0b9ad6e8c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_add_le_fb366f40db4d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_affineSubst_le_685f1ed1ce28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_affineSubst_affineSubst_3d86c1732e84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_affineSubst_one_zero_15c75ac076de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_norm_sum_le_one_2f0d05efeaa4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_mul_le_e992443b279f


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
open MvPolynomial
noncomputable section
open GaussNormBasic
namespace GroundTheory.Heights₂.Heights
namespace GaussNormBasic
theorem _root_.solution : GaussNormBasic.Statement := by
  intro L _ _ _
  refine ⟨fun ι g g' ↦ ⟨gaussNorm_add_le g g', gaussNormOf_mul_le isNonarchimedean_normAbv g g'⟩,
    fun ι κ _ B a hB ha g ↦ gaussNorm_affineSubst_le B a hB ha g, ?_, ?_⟩
  · intro ι _ _ B a hB ha hdet hinv g
    refine le_antisymm (gaussNorm_affineSubst_le B a hB ha g) ?_
    set a' : ι → L := -(B⁻¹.mulVec a)
    have ha' : ∀ i, ‖a' i‖ ≤ 1 := fun i ↦ by
      simp only [a', Pi.neg_apply, norm_neg, Matrix.mulVec, dotProduct]
      exact norm_sum_le_one _ _ fun j _ ↦ by
        rw [norm_mul]; exact mul_le_one₀ (hinv i j) (norm_nonneg _) (ha j)
    have hcomp : affineSubst B⁻¹ a' (affineSubst B a g) = g := by
      rw [affineSubst_affineSubst, Matrix.mul_nonsing_inv _ hdet]
      have : B.mulVec a' + a = 0 := by
        simp only [a', Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
          Matrix.one_mulVec, neg_add_cancel]
      rw [this, affineSubst_one_zero]
    calc gaussNormOf (normAbv L) g
        = gaussNormOf (normAbv L) (affineSubst B⁻¹ a' (affineSubst B a g)) := by rw [hcomp]
      _ ≤ _ := gaussNorm_affineSubst_le _ _ hinv ha' _
  · intro ι κ _ _ P hP hsurj g
    classical
    refine le_antisymm (gaussNorm_affineSubst_le P 0 hP (fun _ ↦ by simp) g) ?_
    choose x hx hPx using fun i : ι ↦ hsurj (Pi.single i 1) fun j ↦ by
      rw [Pi.single_apply]; split_ifs <;> simp
    let S : Matrix κ ι L := fun k i ↦ x i k
    have hPS : P * S = 1 := by
      ext j i
      have := congrFun (hPx i) j
      simp only [Matrix.mulVec, dotProduct] at this
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [S, this, Pi.single_apply]
    have hcomp : affineSubst S 0 (affineSubst P 0 g) = g := by
      rw [affineSubst_affineSubst, hPS, Matrix.mulVec_zero, add_zero, affineSubst_one_zero]
    calc gaussNormOf (normAbv L) g
        = gaussNormOf (normAbv L) (affineSubst S 0 (affineSubst P 0 g)) := by rw [hcomp]
      _ ≤ _ := gaussNorm_affineSubst_le _ _ (fun k i ↦ hx i k) (fun _ ↦ by simp) _
end GaussNormBasic
end GroundTheory.Heights₂.Heights
