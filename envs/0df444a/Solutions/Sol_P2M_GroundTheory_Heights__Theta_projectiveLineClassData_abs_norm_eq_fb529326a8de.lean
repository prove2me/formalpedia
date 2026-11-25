-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_abs_norm_eq_fb529326a8de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:56.011509+00:00
-- url     : https://prove2.me/submissions/3cc3119d-7880-4956-9e1f-fca55dd6b343

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_RealEisensteinNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_eq_mk_5796c1fd3e82
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_isComplex_mk_14edc12b1c27

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding UpperHalfPlane
open scoped nonZeroDivisors ComplexConjugate
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (x : K) : |((Algebra.norm ℚ x : ℚ) : ℝ)| = ‖σ x‖ ^ 2 := by
  classical
  have h := prod_eq_abs_norm x
  have hall : ∀ w : InfinitePlace K, w = mk σ := eq_mk hK σ hσ
  rw [Finset.prod_eq_single_of_mem (mk σ) (Finset.mem_univ _)
    (fun w _ hw => absurd (hall w) hw)] at h
  have hm : mult (mk σ) = 2 := by
    rw [mult, if_neg (not_isReal_iff_isComplex.mpr (isComplex_mk σ hσ))]
  rw [hm, apply] at h
  rw [h, Rat.cast_abs]
end GroundTheory.Heights₂.Theta.projectiveLineClassData
