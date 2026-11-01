-- Prove2me | solution 1 for StrategicPolicy.StochasticOpt.strategic_beats_nonstrategic
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-31T15:05:17.914031+00:00
-- url     : https://prove2.me/submissions/fd96616e-ecdd-4249-ade3-523f0231aa7b

import Mathlib
import Definitions.Def_StrategicPolicy_StochasticOpt_Setting
import Definitions.Def_StrategicPolicy_StochasticOpt_Example
import Theorems.Thm_StrategicPolicy_StochasticOpt_induced_transport

open StrategicPolicy.StochasticOpt

/-- If the tie set of an individual at `i` is the singleton `{j}`, the best response is `j`. -/
private lemma br_eq_of_tieSet_eq {m : ℕ} [NeZero m] (c : Fin m → Fin m → ℝ) (q π : Fin m → ℝ)
    (i j : Fin m) (h : tieSet c q π i = {j}) : br c q π i = j := by
  unfold br
  simp [h]

/-! ### Best responses to the all-ones policy `𝟙 = (1, 1, 1)`

Under `𝟙` every destination yields benefit `1`, so an individual maximizes `1 - c(x_i, x_k)` by
avoiding every positive cost. Individuals at `x = 1` are indifferent among all three (free)
destinations and tie-break (ii) keeps them at the highest outcome `x = 1`; individuals at
`x = 2` are indifferent between `x = 2` and `x = 3` (both free) and tie-break (ii) keeps them
at `x = 2`; individuals at `x = 3` stay, since both upward moves cost. -/

private lemma argmax1_two : argmaxSet c0 (fun _ : Fin 3 => (1 : ℝ)) 2 = {2} := by
  ext k
  fin_cases k <;> simp [argmaxSet, c0, Fin.forall_fin_succ]
  norm_num

private lemma argmax1_one : argmaxSet c0 (fun _ : Fin 3 => (1 : ℝ)) 1 = {1, 2} := by
  ext k
  fin_cases k <;> simp [argmaxSet, c0, Fin.forall_fin_succ] <;> norm_num

private lemma argmax1_zero : argmaxSet c0 (fun _ : Fin 3 => (1 : ℝ)) 0 = {0, 1, 2} := by
  ext k
  fin_cases k <;> simp [argmaxSet, c0, Fin.forall_fin_succ]

private lemma tie1_two : tieSet c0 q0 (fun _ : Fin 3 => (1 : ℝ)) 2 = {2} := by
  ext k
  fin_cases k <;> simp [tieSet, argmax1_two, q0]

private lemma tie1_one : tieSet c0 q0 (fun _ : Fin 3 => (1 : ℝ)) 1 = {1} := by
  ext k
  fin_cases k <;> simp [tieSet, argmax1_one, q0] <;> norm_num

private lemma tie1_zero : tieSet c0 q0 (fun _ : Fin 3 => (1 : ℝ)) 0 = {0} := by
  ext k
  fin_cases k <;> simp [tieSet, argmax1_zero, q0] <;> norm_num

theorem solution :
    uNS p0 q0 γ0 (fun _ => 1) < u p0 q0 γ0 c0 ![1, 7 / 10, 0] ∧
      u p0 q0 γ0 c0 (fun _ => 1) < u p0 q0 γ0 c0 ![1, 7 / 10, 0] := by
  -- best responses to π* = (1, 0.7, 0): br(3) = 2, br(2) = 1, br(1) = 1 (the transport lemma)
  obtain ⟨h2, h1, h0⟩ := induced_transport
  -- best responses to the all-ones policy: everybody stays
  have e2 := br_eq_of_tieSet_eq _ _ _ _ _ tie1_two
  have e1 := br_eq_of_tieSet_eq _ _ _ _ _ tie1_one
  have e0 := br_eq_of_tieSet_eq _ _ _ _ _ tie1_zero
  -- expand both utilities as explicit three-term sums: 0.48 < 0.66 and 0.48 < 0.66
  simp only [u, uNS, Fin.sum_univ_three, h2, h1, h0, e2, e1, e0]
  simp [p0, q0, γ0]
  norm_num
