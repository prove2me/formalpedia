-- Prove2me | solution 1 for PI.QuotInvW.mm_assoc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:31:09.546431+00:00
-- url     : https://prove2.me/submissions/32abd7e3-9969-44a9-a4d7-cb27efd7e0b7

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
theorem _root_.solution (a b c : MtM m) : mm (mm a b) c = mm a (mm b c) := by
  change (Matrix.of a * Matrix.of b * Matrix.of c : Matrix (Fin m) (Fin m) ℂ) =
    Matrix.of a * (Matrix.of b * Matrix.of c)
  exact Matrix.mul_assoc _ _ _
end PI.QuotInvW
