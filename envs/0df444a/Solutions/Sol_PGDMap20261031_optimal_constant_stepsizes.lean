-- Prove2me | solution 1 for PGDMap20261031.optimal_constant_stepsizes
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T13:05:32.648914+00:00
-- url     : https://prove2.me/submissions/8d338c55-c602-487c-8c31-e5610fb60e4f

import Mathlib.Tactic
import Theorems.Thm_PGDMap20261031_step_balance
import Theorems.Thm_PGDMap20261031_step_monotonicity
import Theorems.Thm_PGDMap20261031_step_scalar_equations
import Theorems.Thm_PGDMap20261031_step_asymptotics
import Theorems.Thm_PGDMap20261031_step_two_updates
import Theorems.Thm_PGDMap20261031_step_one_update
open PGDMap20261031

theorem solution : FullStepsizeTheorem := by
  exact ⟨PGDMap20261031.step_balance,
    PGDMap20261031.step_monotonicity,
    PGDMap20261031.step_scalar_equations,
    PGDMap20261031.step_asymptotics,
    PGDMap20261031.step_two_updates,
    PGDMap20261031.step_one_update⟩
