-- Prove2me | solution 1 for PandoraBO.Private20261023.optimal_policy_cost_reward_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:05:29.381168+00:00
-- url     : https://prove2.me/submissions/f3bf6335-7384-40aa-86d4-f31db078fe40

import Definitions.Def_PandoraBO_Model
import Mathlib.Tactic.Linarith

/-!
An unconditional algebraic ingredient for the monotone-policy-limit goals:
increasing a nonnegative cost multiplier can only decrease expected cost and
expected reward among globally optimal policies. No policy construction or
unproved mission milestone is imported.
-/

set_option autoImplicit false

open PandoraBO

theorem solution {n : ℕ} (M : Instance n) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s < t) (π ρ : Policy n)
    (hπ : optimal M s π) (hρ : optimal M t ρ) :
    expectedCost M ρ ≤ expectedCost M π ∧
      expectedReward M ρ ≤ expectedReward M π := by
  have hleft := hπ ρ
  have hright := hρ π
  simp only [value] at hleft hright
  have hscaled : (t - s) * (expectedCost M ρ - expectedCost M π) ≤ 0 := by
    nlinarith
  have hcost : expectedCost M ρ ≤ expectedCost M π :=
    sub_nonpos.mp (nonpos_of_mul_nonpos_right hscaled (sub_pos.mpr hst))
  refine ⟨hcost, ?_⟩
  have hweighted : 0 ≤ s * (expectedCost M π - expectedCost M ρ) :=
    mul_nonneg hs (sub_nonneg.mpr hcost)
  nlinarith
