-- Prove2me | solution 1 for SpherePacking.harmonicDimension_choose_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/010cdebd-555a-4f49-80d5-dc8769427c38

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
open scoped Nat Topology
namespace SpherePacking
theorem _root_.solution
    {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    (n + k - 2).choose k ≤ Gegenbauer.harmonicDimension n k ∧
      Gegenbauer.harmonicDimension n k ≤ 2 * (n + k - 2).choose k := by
  cases k with
  | zero => omega
  | succ i =>
      have hindex : n + (i + 1) - 2 = n + i - 1 := by
        omega
      have hpascal :
          (n + i - 1).choose (i + 1) =
            (n + i - 2).choose i +
              (n + i - 2).choose (i + 1) := by
        have h := Nat.choose_succ_succ (n + i - 2) i
        have harg : (n + i - 2).succ = n + i - 1 := by
          omega
        simpa only [harg, Nat.succ_eq_add_one] using h
      simp only [Gegenbauer.harmonicDimension_succ, hindex]
      constructor <;> omega
end SpherePacking
