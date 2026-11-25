-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_smul_measure_fd7243322d3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:18:31.955299+00:00
-- url     : https://prove2.me/submissions/f7d1fa44-678b-480e-93be-84cbe5dc8f89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol

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
open MeasureTheory Measure Set
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution {α : Type*} [MeasurableSpace α] (μ : Measure α) {c : ENNReal}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (s : Set α) (g : α → ℝ) :
    ⨍ x in s, g x ∂(c • μ) = ⨍ x in s, g x ∂μ := by
  have hc : 0 < c.toReal := ENNReal.toReal_pos hc0 hct
  rw [setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_measure, measureReal_def,
    measureReal_def]
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [mul_inv]
  field_simp
end GroundTheory.Heights₂.Heights.SphereMean
