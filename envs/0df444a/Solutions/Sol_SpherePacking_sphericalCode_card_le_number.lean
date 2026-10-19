-- Prove2me | solution 1 for SpherePacking.sphericalCode_card_le_number
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/00d7bd5f-cc50-4221-b33f-7b8c7c7e218c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open SpherePacking
namespace SpherePacking
theorem _root_.solution {n : ℕ} {s : ℝ}
    (C : SphericalCode n s) :
    (C.points.card : ℕ∞) ≤ sphericalCodeNumber n s := by
  exact le_iSup (fun D : SphericalCode n s => (D.points.card : ℕ∞)) C
end SpherePacking
