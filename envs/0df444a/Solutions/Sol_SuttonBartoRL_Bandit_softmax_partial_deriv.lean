-- Prove2me | solution 1 for SuttonBartoRL.Bandit.softmax_partial_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:43:18.756716+00:00
-- url     : https://prove2.me/submissions/8cf3e948-fc2d-41b1-ac99-4512121bdc50

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_GradientBandit

set_option autoImplicit false

open SuttonBartoRL.Bandit in
theorem softmax_upd_coord_deriv_6bb {k : ℕ} (H : Fin k → ℝ) (a b : Fin k) (y : ℝ) :
    HasDerivAt (fun h => Function.update H a h b) (if b = a then 1 else 0) y := by
  by_cases hb : b = a
  · subst hb
    simp only [Function.update_self, if_true]
    exact hasDerivAt_id y
  · simp only [Function.update_of_ne hb, if_neg hb]
    exact hasDerivAt_const y (H b)

open SuttonBartoRL.Bandit in
theorem solution {k : ℕ} (H : Fin k → ℝ) (x a : Fin k) :
    HasDerivAt (fun h => softmaxPolicy (Function.update H a h) x)
      (softmaxPolicy H x * ((if a = x then 1 else 0) - softmaxPolicy H a)) (H a) := by
  have hN := (softmax_upd_coord_deriv_6bb H a x (H a)).exp
  have hS : HasDerivAt (fun h => ∑ b ∈ Finset.univ, Real.exp (Function.update H a h b))
      (∑ b ∈ Finset.univ, Real.exp (Function.update H a (H a) b) * (if b = a then 1 else 0)) (H a) :=
    HasDerivAt.fun_sum (fun b _ => (softmax_upd_coord_deriv_6bb H a b (H a)).exp)
  have hpos : 0 < ∑ b, Real.exp (H b) :=
    Finset.sum_pos (fun b _ => Real.exp_pos _) ⟨x, Finset.mem_univ x⟩
  have hD := hN.div hS (by simp only [Function.update_eq_self]; exact hpos.ne')
  unfold softmaxPolicy
  have hu : Function.update H a (H a) = H := Function.update_eq_self a H
  rw [hu] at hD
  have hsum : (∑ b, Real.exp (H b) * (if b = a then (1:ℝ) else 0)) = Real.exp (H a) := by
    simp [Finset.sum_ite_eq']
  rw [hsum] at hD
  refine hD.congr_deriv ?_
  have hS0 := hpos.ne'
  by_cases h : a = x
  · subst h
    simp only [if_true]
    field_simp
  · simp only [if_neg h, if_neg (Ne.symm h)]
    field_simp
