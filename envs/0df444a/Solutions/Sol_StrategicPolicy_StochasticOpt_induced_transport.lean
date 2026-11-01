-- Prove2me | solution 1 for StrategicPolicy.StochasticOpt.induced_transport
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-31T15:03:52.057321+00:00
-- url     : https://prove2.me/submissions/16e195c2-adb7-4b63-9c28-4e17e0fcec46

import Mathlib
import Definitions.Def_StrategicPolicy_StochasticOpt_Setting
import Definitions.Def_StrategicPolicy_StochasticOpt_Example

open StrategicPolicy.StochasticOpt

/-- If the tie set of an individual at `i` is the singleton `{j}`, the best response is `j`. -/
private lemma br_eq_of_tieSet_eq {m : ℕ} [NeZero m] (c : Fin m → Fin m → ℝ) (q π : Fin m → ℝ)
    (i j : Fin m) (h : tieSet c q π i = {j}) : br c q π i = j := by
  unfold br
  simp [h]

/-! ### Best responses to `π* = (1, 0.7, 0)`

For an individual starting at `x_i` the objective is `π*(x_k) - c(x_i, x_k)`; we compute its
maximizers (`argmaxSet`) and then apply tie-break (ii) (`tieSet`). -/

/-- `x = 3` (index 2): the payoffs are `1 - 1.2 = -0.2`, `0.7 - 0.3 = 0.4`, `0 - 0 = 0`,
so the unique maximizer is `x = 2` (index 1). -/
private lemma argmax_two : argmaxSet c0 ![1, 7 / 10, 0] 2 = {1} := by
  ext k
  fin_cases k <;> simp [argmaxSet, c0, Fin.forall_fin_succ] <;> norm_num

/-- `x = 2` (index 1): the payoffs are `1 - 0.3 = 0.7`, `0.7 - 0 = 0.7`, `0 - 0 = 0`,
so staying and moving to `x = 1` tie. -/
private lemma argmax_one : argmaxSet c0 ![1, 7 / 10, 0] 1 = {0, 1} := by
  ext k
  fin_cases k <;> simp [argmaxSet, c0, Fin.forall_fin_succ] <;> norm_num

/-- `x = 1` (index 0): the payoffs are `1`, `0.7`, `0`, so staying is the unique maximizer. -/
private lemma argmax_zero : argmaxSet c0 ![1, 7 / 10, 0] 0 = {0} := by
  ext k
  fin_cases k <;> simp [argmaxSet, c0, Fin.forall_fin_succ] <;> norm_num

private lemma tie_two : tieSet c0 q0 ![1, 7 / 10, 0] 2 = {1} := by
  ext k
  fin_cases k <;> simp [tieSet, argmax_two, q0]

/-- The tie at `x = 2` is broken toward the higher outcome: `q(x_1) = 1 > 0.7 = q(x_2)`. -/
private lemma tie_one : tieSet c0 q0 ![1, 7 / 10, 0] 1 = {0} := by
  ext k
  fin_cases k <;> simp [tieSet, argmax_one, q0] <;> norm_num

private lemma tie_zero : tieSet c0 q0 ![1, 7 / 10, 0] 0 = {0} := by
  ext k
  fin_cases k <;> simp [tieSet, argmax_zero, q0]

theorem solution :
    br c0 q0 ![1, 7 / 10, 0] 2 = 1 ∧ br c0 q0 ![1, 7 / 10, 0] 1 = 0 ∧
      br c0 q0 ![1, 7 / 10, 0] 0 = 0 :=
  ⟨br_eq_of_tieSet_eq _ _ _ _ _ tie_two, br_eq_of_tieSet_eq _ _ _ _ _ tie_one,
    br_eq_of_tieSet_eq _ _ _ _ _ tie_zero⟩
