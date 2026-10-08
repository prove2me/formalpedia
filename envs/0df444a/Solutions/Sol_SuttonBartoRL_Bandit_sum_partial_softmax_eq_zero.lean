-- Prove2me | solution 1 for SuttonBartoRL.Bandit.sum_partial_softmax_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:31:01.960194+00:00
-- url     : https://prove2.me/submissions/401b742b-4da3-4aa8-aec6-d8587da49d35

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_GradientBandit

open SuttonBartoRL.Bandit in
theorem d4f7fdc0_update_diff {k : ℕ} (H : Fin k → ℝ) (a b : Fin k) :
    Differentiable ℝ (fun h : ℝ => Function.update H a h b) := by
  by_cases hb : b = a
  · subst hb
    simp only [Function.update_self]
    exact differentiable_id
  · simp only [Function.update_of_ne hb]
    exact differentiable_const _

open SuttonBartoRL.Bandit in
theorem solution {k : ℕ} (H : Fin k → ℝ) (a : Fin k) :
    ∑ x, partialDeriv (fun H' => softmaxPolicy H' x) H a = 0 := by
  unfold partialDeriv
  have hdiff : ∀ x ∈ (Finset.univ : Finset (Fin k)),
      DifferentiableAt ℝ (fun h => softmaxPolicy (Function.update H a h) x) (H a) := by
    intro x _
    unfold softmaxPolicy
    apply DifferentiableAt.div
    · exact ((d4f7fdc0_update_diff H a x) (H a)).exp
    · apply DifferentiableAt.fun_sum
      intro b _
      exact ((d4f7fdc0_update_diff H a b) (H a)).exp
    · exact (Finset.sum_pos (fun b _ => Real.exp_pos _) ⟨a, Finset.mem_univ _⟩).ne'
  rw [← deriv_fun_sum hdiff]
  have hconst : (fun h => ∑ x, softmaxPolicy (Function.update H a h) x) = fun _ => (1 : ℝ) := by
    funext h
    unfold softmaxPolicy
    rw [← Finset.sum_div]
    exact div_self (Finset.sum_pos (fun b _ => Real.exp_pos _) ⟨a, Finset.mem_univ _⟩).ne'
  rw [hconst]
  simp
