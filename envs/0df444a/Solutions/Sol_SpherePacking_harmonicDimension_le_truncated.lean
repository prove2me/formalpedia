-- Prove2me | solution 1 for SpherePacking.harmonicDimension_le_truncated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/a9e3a17e-54e5-4519-bdec-e6a6ee9acbb7

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
    (n k L : ℕ) (hkl : k ≤ L) :
    Gegenbauer.harmonicDimension n k ≤
      truncatedHarmonicDimension n k L := by
  unfold truncatedHarmonicDimension
  apply Finset.single_le_sum
  · intro i hi
    exact Nat.zero_le _
  · exact Finset.mem_Icc.mpr ⟨le_rfl, hkl⟩
end SpherePacking
