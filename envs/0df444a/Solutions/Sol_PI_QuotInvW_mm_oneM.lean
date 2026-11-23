-- Prove2me | solution 1 for PI.QuotInvW.mm_oneM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:20.60157+00:00
-- url     : https://prove2.me/submissions/3af65f21-8113-41b6-b966-d8c9ae28cc8a

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
theorem _root_.solution (a : MtM m) : mm a oneM = a := by
  funext i j
  show (Matrix.of a * 1 : Matrix (Fin m) (Fin m) ℂ) i j = a i j
  rw [Matrix.mul_one]
  rfl
end PI.QuotInvW
