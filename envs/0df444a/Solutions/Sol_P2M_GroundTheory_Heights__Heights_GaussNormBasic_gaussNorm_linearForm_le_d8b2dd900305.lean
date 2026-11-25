-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_linearForm_le_d8b2dd900305
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:02:27.506263+00:00
-- url     : https://prove2.me/submissions/ade6b653-d963-4342-acc6-d5635b70f0d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_normAbv_apply_a22c800c8e89
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_add_le_fb366f40db4d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_sum_le_df58dd8b246b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_monomial_le_c481412a16d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_C_6e81e4d023f3


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
theorem _root_.solution {κ : Type*} [Fintype κ] (b : κ → L) (c : L)
    (hb : ∀ j, ‖b j‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    gaussNormOf (normAbv L) (∑ j, C (b j) * X j + C c : MvPolynomial κ L) ≤ 1 := by
  refine (gaussNorm_add_le _ _).trans (max_le ?_ ?_)
  · refine gaussNorm_sum_le _ _ zero_le_one fun j _ ↦ ?_
    rw [C_mul_X_eq_monomial]
    exact (gaussNorm_monomial_le _ _).trans (hb j)
  · rw [gaussNormOf_C, normAbv_apply]; exact hc
end GroundTheory.Heights₂.Heights.GaussNormBasic
