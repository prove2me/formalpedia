-- Prove2me | solution 1 for SpherePacking.truncatedHarmonicDimension_le_successor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/cda15619-d4a5-45d6-8449-87404540a6fc

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_Gegenbauer_harmonicDimension_branch_sum

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
    {n : ℕ} (hn : 2 ≤ n) (k L : ℕ) :
    truncatedHarmonicDimension n k L ≤
      Gegenbauer.harmonicDimension (n + 1) L := by
  calc
    truncatedHarmonicDimension n k L =
        ∑ i ∈ Finset.Icc k L,
          Gegenbauer.harmonicDimension n i := rfl
    _ ≤ ∑ i ∈ Finset.range (L + 1),
          Gegenbauer.harmonicDimension n i := by
      apply Finset.sum_le_sum_of_subset
      intro i hi
      have hi' := (Finset.mem_Icc.mp hi).2
      apply Finset.mem_range.mpr
      omega
    _ = Gegenbauer.harmonicDimension (n + 1) L :=
      Gegenbauer.harmonicDimension_branch_sum hn L
end SpherePacking
