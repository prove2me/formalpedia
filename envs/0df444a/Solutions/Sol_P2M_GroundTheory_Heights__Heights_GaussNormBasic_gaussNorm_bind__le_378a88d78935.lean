-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_bind__le_378a88d78935
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:02:50.760811+00:00
-- url     : https://prove2.me/submissions/8a23a227-0bd0-4ffa-87cd-c3ce09982d5e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_isNonarchimedean_normAbv_86b0b9ad6e8c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_sum_le_df58dd8b246b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_prod_le_one_2cd74388c558
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_pow_le_one_601ccd826390
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_C_6e81e4d023f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_mul_le_e992443b279f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_nonneg_e5b131e01688
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_gaussNormOf_6379dd47bf35


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
open GroundTheory.Heights₂.Heights.GaussNormBasic
variable {L : Type*} [NormedField L] [IsUltrametricDist L]
namespace GroundTheory.Heights₂.Heights.GaussNormBasic
theorem _root_.solution {ι κ : Type*} (f : ι → MvPolynomial κ L)
    (hf : ∀ i, gaussNormOf (normAbv L) (f i) ≤ 1) (g : MvPolynomial ι L) :
    gaussNormOf (normAbv L) (bind₁ f g) ≤ gaussNormOf (normAbv L) g := by
  conv_lhs => rw [g.as_sum, map_sum]
  refine gaussNorm_sum_le _ _ (gaussNormOf_nonneg _ g) fun m _ ↦ ?_
  rw [bind₁_monomial]
  refine (gaussNormOf_mul_le isNonarchimedean_normAbv _ _).trans ?_
  rw [gaussNormOf_C]
  have h1 := gaussNorm_prod_le_one m.support (fun i ↦ f i ^ m i)
    fun i _ ↦ gaussNorm_pow_le_one _ (hf i) _
  calc normAbv L (g.coeff m) * gaussNormOf (normAbv L) (∏ i ∈ m.support, f i ^ m i)
      ≤ normAbv L (g.coeff m) * 1 :=
        mul_le_mul_of_nonneg_left h1 ((normAbv L).nonneg _)
    _ ≤ gaussNormOf (normAbv L) g := by rw [mul_one]; exact le_gaussNormOf _ g m
end GroundTheory.Heights₂.Heights.GaussNormBasic
