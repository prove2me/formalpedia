-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeTangentAverage_proof_3157c23abeec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:45:29.192819+00:00
-- url     : https://prove2.me/submissions/20b32f6f-1cde-4f32-8c6d-b1d43e8cda43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_coneTangent_self_8b2ec418ba5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isClosed_coneSet_ab7a54df5c4b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sFinite_restrict_of_ball_7c63509fd53a

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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeTangentAverage
theorem _root_.solution (hMass : ConeLocalMass.Statement)
    (hMeas : ConeJacMeasurable.Statement) (hDim : ConeTangentDim.Statement)
    (hInv : TangentGaussInvariant.Statement) : ConeTangentAverage.Statement := by
  intro n m h J hJ hm hmn hfib
  have : SFinite ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
      Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J)) :=
    sFinite_restrict_of_ball _ _ (hMass n m h J hJ hm hmn hfib)
  have hG : Measurable fun π : Fin m → Fin n → ℂ => matGauss π := by
    unfold matGauss
    exact (by fun_prop : Continuous fun π : Fin m → Fin n → ℂ =>
      Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2)).measurable.ennreal_ofReal
  have hP : Continuous fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => linProj p.1 p.2 := by
    unfold linProj
    fun_prop
  have hF : AEMeasurable (Function.uncurry fun (π : Fin m → Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) =>
      matGauss π * ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
        ENNReal.ofReal (coneJac h J π y)))
      ((volume : Measure (Fin m → Fin n → ℂ)).prod
        ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J))) :=
    (hG.comp measurable_fst).aemeasurable.mul
      (((measurable_one.indicator Metric.isOpen_ball.measurableSet).comp hP.measurable).aemeasurable.mul
        (hMeas n m h J hJ hm hmn hfib).ennreal_ofReal)
  rw [show (fun π : Fin m → Fin n → ℂ => matGauss π *
      ∫⁻ y in coneSet h J, (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
        ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))) =
      fun π => ∫⁻ y in coneSet h J, matGauss π *
        ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y)) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) from
    funext fun π => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm,
    lintegral_lintegral_swap hF]
  refine lintegral_congr_ae ?_
  filter_upwards [hDim n m h J hJ hm hmn hfib, ae_restrict_mem (isClosed_coneSet h J).measurableSet]
    with y hy hyC
  simp only [← mul_assoc]
  exact hInv n m hm hmn _ hy y (mem_coneTangent_self h hJ hyC)
end ConeTangentAverage
end GroundTheory.Heights₂.Heights
