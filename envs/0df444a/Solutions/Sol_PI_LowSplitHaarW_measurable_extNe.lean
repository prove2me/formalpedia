-- Prove2me | solution 1 for PI.LowSplitHaarW.measurable_extNe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:12.304278+00:00
-- url     : https://prove2.me/submissions/8cefff9f-cd24-4c9a-940e-4c61124b7846

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerShearHaar_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerShearHaar_MeasurePreservingOfCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open PI PI.LowSplitHaarW
namespace PI.LowSplitHaarW
theorem _root_.solution {ι : Type} [DecidableEq ι] (a : ι) : Measurable (extNe a) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases h : j ≠ a
  · simp only [extNe, dif_pos h]
    exact measurable_pi_apply _
  · simp only [extNe, dif_neg h]
    exact measurable_const
end PI.LowSplitHaarW
