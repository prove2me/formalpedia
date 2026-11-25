-- Prove2me | solution 1 for PI.QuotInvW.measurable_mm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:16:13.108108+00:00
-- url     : https://prove2.me/submissions/43f9760a-747e-4445-a39d-e636b052a67a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
import Theorems.Thm_PI_QuotInvW_continuous_mm

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
theorem _root_.solution : Measurable (fun p : MtM m × MtM m => mm p.1 p.2) :=
  continuous_mm.measurable
end PI.QuotInvW
