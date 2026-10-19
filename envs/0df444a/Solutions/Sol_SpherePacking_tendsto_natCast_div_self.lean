-- Prove2me | solution 1 for SpherePacking.tendsto_natCast_div_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/66413c67-b8a9-4e0e-800a-a6f8d7737c3d

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
open SpherePacking
noncomputable section
set_option autoImplicit false
open Filter Real
open scoped BigOperators Nat Topology
namespace SpherePacking
theorem _root_.solution :
    Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
  have heq :
      (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => (n : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    exact (div_self hn').symm
  exact tendsto_const_nhds.congr' heq
end SpherePacking
