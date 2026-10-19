-- Prove2me | solution 1 for SpherePacking.truncatedDimensionQuotient_le_harmonicDimensionQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/2bb24b43-750a-4b34-8caa-1da0f372db96

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_truncatedHarmonicDimension_le_successor

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
    truncatedDimensionQuotient a b n ≤
      harmonicDimensionQuotient a b n := by
  unfold truncatedDimensionQuotient harmonicDimensionQuotient
    Gegenbauer.fibreDimension
  apply div_le_div_of_nonneg_right
  · exact_mod_cast truncatedHarmonicDimension_le_successor
      (by omega : 2 ≤ n)
      ⌊b * (n : ℝ)⌋₊ ⌊a * (n : ℝ)⌋₊
  · exact_mod_cast
      (Gegenbauer.harmonicDimension_pos
        (by omega : 2 ≤ n - 1) ⌊b * (n : ℝ)⌋₊).le
end SpherePacking
