-- Prove2me | solution 1 for PandoraBO.Private20261023.active_budget_dual_multiplier_positive
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T00:28:38.068187+00:00
-- url     : https://prove2.me/submissions/b7a18e9b-7148-455f-811b-797714d2f1b0

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_zero_dual_minimum_feasible_gittins

/-!
Tracked reduction to the feasible zero-multiplier milestone. Its globally
optimal zero-cost witness supplies the bound needed for the real supremum;
there is no extra boundedness assumption and no circular use of the main goal.
-/

set_option autoImplicit false

open PandoraBO

theorem solution {n : ℕ} (M : Instance n)
    (B multiplier : ℝ) (_hslater : ∃ i : Box n, M.cost i < B)
    (hactive : genuinelyActiveBudget M B) (hmin : dualMinimizer M B multiplier) :
    0 < multiplier := by
  apply lt_of_le_of_ne hmin.1
  intro hzero
  have hminzero : dualMinimizer M B 0 := by
    simpa only [← hzero] using hmin
  obtain ⟨π, _hindex, hfeasible, hfull, hopt⟩ :=
    PandoraBO.Private20261023.zero_dual_minimum_feasible_gittins M B hminzero
  have hbound : BddAbove {r : ℝ | ∃ ρ : Policy n,
      budgetFeasible M B ρ ∧ r = expectedReward M ρ} := by
    refine ⟨expectedReward M π, ?_⟩
    rintro r ⟨ρ, _hρfeasible, rfl⟩
    simpa only [value, zero_mul, sub_zero] using hopt ρ
  have hsup : expectedReward M π ≤ budgetValue M B :=
    le_csSup hbound ⟨π, hfeasible, rfl⟩
  have hgap : budgetValue M B < fullInformationReward M := hactive.2
  exact (not_lt_of_ge (hfull ▸ hsup)) hgap
