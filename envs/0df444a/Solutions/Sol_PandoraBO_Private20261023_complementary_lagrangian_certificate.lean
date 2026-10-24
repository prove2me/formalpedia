-- Prove2me | solution 1 for PandoraBO.Private20261023.complementary_lagrangian_certificate
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-23T23:42:19.886211+00:00
-- url     : https://prove2.me/submissions/3cfb7ac6-8298-4fc9-b862-4baab5e75733

import Definitions.Def_PandoraBO_Model

set_option autoImplicit false

open PandoraBO

/-- Feasibility and complementary slackness certify budget optimality. -/
theorem solution {n : ℕ} (M : Instance n)
    (B multiplier : ℝ) (hnonneg : 0 ≤ multiplier) (π : Policy n)
    (hopt : optimal M multiplier π) (hfeasible : budgetFeasible M B π)
    (hcomp : complementarySlackness M B multiplier π) :
    budgetOptimal M B π := by
  refine ⟨hfeasible, ?_⟩
  intro ρ hρ
  have hρ_cost : expectedCost M ρ ≤ B := hρ
  have hweightedBudget : multiplier * B = multiplier * expectedCost M π := by
    have hzero : multiplier * (B - expectedCost M π) = 0 := hcomp
    rw [mul_sub] at hzero
    exact sub_eq_zero.mp hzero
  have hcost : multiplier * expectedCost M ρ ≤
      multiplier * expectedCost M π := by
    calc
      multiplier * expectedCost M ρ ≤ multiplier * B :=
        mul_le_mul_of_nonneg_left hρ_cost hnonneg
      _ = multiplier * expectedCost M π := hweightedBudget
  have hvalue : expectedReward M ρ - multiplier * expectedCost M ρ ≤
      expectedReward M π - multiplier * expectedCost M π := hopt ρ
  calc
    expectedReward M ρ =
        (expectedReward M ρ - multiplier * expectedCost M ρ) +
          multiplier * expectedCost M ρ :=
      (sub_add_cancel (expectedReward M ρ) (multiplier * expectedCost M ρ)).symm
    _ ≤ (expectedReward M π - multiplier * expectedCost M π) +
          multiplier * expectedCost M π := add_le_add hvalue hcost
    _ = expectedReward M π :=
      sub_add_cancel (expectedReward M π) (multiplier * expectedCost M π)
