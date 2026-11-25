-- Prove2me | solution 1 for QPK.ennreal_eq_one_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:21.741986+00:00
-- url     : https://prove2.me/submissions/c8d4647b-4108-44f3-b746-b7a079f8bda9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_ConjugationInvariantMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open scoped ENNReal
open QPK
namespace QPK
theorem _root_.solution {a b : ℝ≥0∞} (h0 : b ≠ 0) (ht : b ≠ ⊤) (h : a * b = b) : a = 1 := by
  calc a = a * b / b := (ENNReal.mul_div_cancel_right h0 ht).symm
    _ = b / b := by rw [h]
    _ = 1 := ENNReal.div_self h0 ht
end QPK
