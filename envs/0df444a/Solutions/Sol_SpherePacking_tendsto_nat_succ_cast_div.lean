-- Prove2me | solution 1 for SpherePacking.tendsto_nat_succ_cast_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/f6b2f10f-50a8-443a-b15f-3ccae320c2bc

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
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
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
  have h := tendsto_natCast_div_self.add
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  simpa [Nat.cast_add, add_div] using h
end SpherePacking
