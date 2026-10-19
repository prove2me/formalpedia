-- Prove2me | solution 1 for SpherePacking.sphericalCodeNumber_eq_codes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/d29189ce-cc55-4b00-ad19-641ccf6b8f02

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
theorem _root_.solution (n : ℕ) (s : ℝ) :
    sphericalCodeNumber n s = MetricCodes.sphericalCodeNumber n s := by
  unfold sphericalCodeNumber MetricCodes.sphericalCodeNumber
  exact (sphericalCodeEquiv n s).iSup_congr
    (fun C => congrArg (fun k : ℕ => (k : ℕ∞)) C.toCodes_card)
end SpherePacking
