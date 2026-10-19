-- Prove2me | solution 1 for SpherePacking.harmonicDimensionQuotient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/82ee1dc1-dc3e-458c-a74a-d596d128ba99

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
theorem _root_.solution
    (a b : ℝ) {n : ℕ} (hn : 3 ≤ n) :
    0 < harmonicDimensionQuotient a b n := by
  unfold harmonicDimensionQuotient
  apply div_pos
  · exact_mod_cast
      Gegenbauer.harmonicDimension_pos (by omega : 2 ≤ n + 1)
        ⌊a * (n : ℝ)⌋₊
  · exact_mod_cast
      Gegenbauer.harmonicDimension_pos (by omega : 2 ≤ n - 1)
        ⌊b * (n : ℝ)⌋₊
end SpherePacking
