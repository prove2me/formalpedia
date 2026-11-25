-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_euclid_ne_zero_de4ee5fbccea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:06:49.138604+00:00
-- url     : https://prove2.me/submissions/41a0cee1-0d2f-40eb-baea-d40e5a8afc6f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjDegreeChow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFibreDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_ne_zero_univ_4de5667b5aac

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
open MvPolynomial MeasureTheory Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.ConeFibreDegree
namespace GroundTheory.Heights₂.Heights.ConeFibreDegree
theorem _root_.solution {m : ℕ} (g : MvPolynomial (Fin m) ℂ) (hg : g ≠ 0) :
    ∀ᵐ w : EuclideanSpace ℂ (Fin m), eval (WithLp.ofLp w) g ≠ 0 := by
  let L : EuclideanSpace ℂ (Fin m) ≃L[ℝ] (Fin m → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin m => ℂ)
  have hac : (volume : Measure (EuclideanSpace ℂ (Fin m))).map L ≪ volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have h : ∀ᵐ u ∂(volume : Measure (EuclideanSpace ℂ (Fin m))).map L, eval u g ≠ 0 :=
    hac.ae_le (ae_eval_ne_zero_univ g hg)
  rw [ae_map_iff L.continuous.measurable.aemeasurable] at h
  · exact h
  · exact (isClosed_eq (continuous_eval g) continuous_const).isOpen_compl.measurableSet
end GroundTheory.Heights₂.Heights.ConeFibreDegree
