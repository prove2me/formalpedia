-- Prove2me | solution 1 for PI.QuotInvW.continuous_mm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:11:59.558852+00:00
-- url     : https://prove2.me/submissions/5b7850ad-af4b-4859-b225-2b006d7bcbc7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight

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
theorem _root_.solution : Continuous (fun p : MtM m × MtM m => mm p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [mm, Matrix.mul_apply, Matrix.of_apply]
  fun_prop
end PI.QuotInvW
