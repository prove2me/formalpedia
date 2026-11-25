-- Prove2me | solution 1 for PI.QuotInvW.measurable_mm_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:15.916226+00:00
-- url     : https://prove2.me/submissions/90bf3ea8-7427-4924-85ed-57cb70095c74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
import Theorems.Thm_PI_QuotInvW_measurable_mm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open PI PI.QuotInvW
variable {m : ℕ}
namespace PI.QuotInvW
theorem _root_.solution (a : MtM m) : Measurable (fun b : MtM m => mm a b) :=
  measurable_mm.comp (measurable_const.prodMk measurable_id)
end PI.QuotInvW
