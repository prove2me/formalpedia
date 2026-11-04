-- Prove2me | solution 1 for ThreeSum.BudgetTime.solvedInTime_of_program_contract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:26:09.87402+00:00
-- url     : https://prove2.me/submissions/1b0be481-3ddf-4c71-b45b-12530858b3b6

import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Theorems.Thm_ThreeSum_BudgetTime_time_endStatementBigO_of_eventually_le_compiledBudget

set_option autoImplicit false
open ThreeSum ThreeSum.BudgetTime
open Filter Real ThreeSum.Parameters ThreeSum.StageBounds
  ThreeSum.UniformStageBounds
open scoped Topology
set_option maxHeartbeats 400000
namespace ThreeSum.BudgetTime
theorem _root_.solution (Q : EndStatement.Problem)
    (hprogram : ∀ κ : ℕ, ∃ (P : List EndStatement.Instr) (w : ℕ) (T : ℕ → ℕ)
      (a b C k : ℕ),
      (∀ᶠ n : ℕ in atTop, T n ≤ compiledBudget a b C k n) ∧
      ∀ (n : ℕ) (x : Q.Instance n),
        (∀ z ∈ Q.input x, z.natAbs ≤ n ^ κ) →
        ∀ W ≥ w * (Nat.log2 n + 1), Q.SolvedBy x P W (T n)) :
    Q.SolvedInTime (981 / 500) := by
  intro κ
  obtain ⟨P, w, T, a, b, C, k, hcost, hcorrect⟩ := hprogram κ
  exact ⟨P, w, T, time_endStatementBigO_of_eventually_le_compiledBudget hcost, hcorrect⟩
end ThreeSum.BudgetTime
