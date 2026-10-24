-- Prove2me | solution 1 for PandoraBO.Private20261023.tight_lagrangian_certificate
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-23T23:42:19.292685+00:00
-- url     : https://prove2.me/submissions/57d4f569-de16-4814-920a-1b6808bc822a

import Definitions.Def_PandoraBO_Model

set_option autoImplicit false

open PandoraBO

/-- A Lagrangian optimizer that spends the budget exactly is budget optimal. -/
theorem solution {n : ℕ} (M : Instance n)
    (B multiplier : ℝ) (hnonneg : 0 ≤ multiplier) (π : Policy n)
    (hopt : optimal M multiplier π) (htight : expectedCost M π = B) :
    budgetOptimal M B π := by
  refine ⟨?_, ?_⟩
  · show expectedCost M π ≤ B
    exact le_of_eq htight
  · intro ρ hρ
    have hρ_cost : expectedCost M ρ ≤ B := hρ
    have hcost : multiplier * expectedCost M ρ ≤
        multiplier * expectedCost M π := by
      calc
        multiplier * expectedCost M ρ ≤ multiplier * B :=
          mul_le_mul_of_nonneg_left hρ_cost hnonneg
        _ = multiplier * expectedCost M π :=
          congrArg (fun c : ℝ => multiplier * c) htight.symm
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
