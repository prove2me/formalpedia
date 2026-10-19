-- Prove2me | solution 1 for SpherePacking.tendsto_nat_pred_cast_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/9b8a3b61-f089-489e-a7c7-cc9b05785506

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_nat_sequence_sub_cast_div
import Theorems.Thm_SpherePacking_tendsto_natCast_div_self

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
open SpherePacking
noncomputable section
set_option autoImplicit false
open Filter Real
open scoped BigOperators Nat Topology
namespace SpherePacking
theorem _root_.solution :
    Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
  exact tendsto_nat_sequence_sub_cast_div
    (fun n => n) 1 1 tendsto_id tendsto_natCast_div_self
end SpherePacking
