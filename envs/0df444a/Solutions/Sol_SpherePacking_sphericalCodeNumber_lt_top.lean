-- Prove2me | solution 1 for SpherePacking.sphericalCodeNumber_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/639a617c-7086-46ae-8ef4-01a790c48114

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_sphericalCodeNumber_lt_top
import Theorems.Thm_SpherePacking_sphericalCodeNumber_eq_codes

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
theorem _root_.solution {n : ℕ} {s : ℝ} (hs : s < 1) :
    sphericalCodeNumber n s < ⊤ := by
  rw [sphericalCodeNumber_eq_codes]
  exact MetricCodes.sphericalCodeNumber_lt_top hs
end SpherePacking
