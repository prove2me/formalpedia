-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_normSq_mul_det_2844130a5510
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:06.382436+00:00
-- url     : https://prove2.me/submissions/dc109970-a7f1-493c-a05b-9672191a093a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_RealEisensteinNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul

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
open EtaPeriodLatticeClass
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution (c a b τ : ℂ) (ha : c * a = 1) (hb : c * b = τ) :
    ((‖c‖ ^ 2 : ℝ) : ℂ) * (a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b) =
      -(2 * τ.im * Complex.I) := by
  have hcb : (starRingEnd ℂ) c * (starRingEnd ℂ) b = (starRingEnd ℂ) τ := by
    rw [← map_mul, hb]
  have hca : (starRingEnd ℂ) c * (starRingEnd ℂ) a = 1 := by
    rw [← map_mul, ha, map_one]
  have hn : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * (starRingEnd ℂ) c := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsub : τ - (starRingEnd ℂ) τ = ((2 * τ.im : ℝ) : ℂ) * Complex.I := Complex.sub_conj τ
  rw [hn]
  push_cast at hsub
  linear_combination ((starRingEnd ℂ) c * (starRingEnd ℂ) b) * ha + hcb - (c * b) * hca - hb - hsub
end GroundTheory.Heights₂.Theta.projectiveLineClassData
