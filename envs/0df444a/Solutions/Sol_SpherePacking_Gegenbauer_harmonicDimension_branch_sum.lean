-- Prove2me | solution 1 for SpherePacking.Gegenbauer.harmonicDimension_branch_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/671537f3-0520-4b9c-8e60-cc8a338cea57

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
open Polynomial
open scoped BigOperators
open SpherePacking.Gegenbauer
namespace SpherePacking.Gegenbauer
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    (∑ r ∈ Finset.range (k + 1), harmonicDimension n r) =
      harmonicDimension (n + 1) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      simpa [Finset.sum_range_succ, ih, Nat.add_assoc] using
        (harmonicDimension_branch_step hn k).symm
end SpherePacking.Gegenbauer
