-- Prove2me | solution 1 for PI.QuotInvW.measurable_mm_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:21:50.835849+00:00
-- url     : https://prove2.me/submissions/e2fef7d2-ee60-4d62-bc98-af49a7298c45

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
theorem _root_.solution (b : MtM m) : Measurable (fun a : MtM m => mm a b) :=
  measurable_mm.comp (measurable_id.prodMk measurable_const)
end PI.QuotInvW
