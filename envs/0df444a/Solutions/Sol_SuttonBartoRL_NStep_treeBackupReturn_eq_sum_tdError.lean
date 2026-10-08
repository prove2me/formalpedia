-- Prove2me | solution 1 for SuttonBartoRL.NStep.treeBackupReturn_eq_sum_tdError
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:38:54.716773+00:00
-- url     : https://prove2.me/submissions/c01edb76-c62b-43c8-977b-a794257a73c6

import Mathlib
import Definitions.Def_SuttonBartoRL_NStep_EpisodeReturns

set_option autoImplicit false

theorem tb257_sum_split (f g : ℕ → ℝ) (t m : ℕ) (h : t ≤ m) :
    ∑ k ∈ Finset.Icc t m, f k * ∏ i ∈ Finset.Ioc t k, g i =
      f t + g (t + 1) * ∑ k ∈ Finset.Icc (t + 1) m, f k * ∏ i ∈ Finset.Ioc (t + 1) k, g i := by
  have hI : ∀ a b : ℕ, Finset.Ioc a b = Finset.Icc (a + 1) b := by
    intro a b; ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [Finset.Icc_eq_cons_Ioc h, Finset.sum_cons, hI t m]
  simp only [Finset.Ioc_self, Finset.prod_empty, mul_one]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : t + 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [hI t k, Finset.Icc_eq_cons_Ioc hk', Finset.prod_cons]
  ring

open SuttonBartoRL.NStep in
theorem solution {S A : Type} [Fintype A] [DecidableEq A]
    (π : Policy S A) (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (At : ℕ → A) (T : ℕ)
    (Q : S → A → ℝ) (hterm : ∀ a, Q (St T) a = 0) (t n : ℕ) (hn : 1 ≤ n) (ht : t < T) :
    treeBackupReturn π γ R St At T Q t (t + n) =
      Q (St t) (At t) +
        ∑ k ∈ Finset.Icc t (min (t + n - 1) (T - 1)),
          expectedTDError π γ R St At Q k *
            ∏ i ∈ Finset.Ioc t k, γ * π.prob (St i) (At i) := by
  induction n generalizing t with
  | zero => omega
  | succ n ih =>
    rw [treeBackupReturn]
    by_cases h1 : T ≤ t + 1
    · rw [if_pos h1]
      have hT : T = t + 1 := by omega
      have hm : min (t + (n + 1) - 1) (T - 1) = t := by omega
      rw [hm, Finset.Icc_self, Finset.sum_singleton, Finset.Ioc_self, Finset.prod_empty, mul_one]
      have hV : expectedApproxValue π Q (St (t + 1)) = 0 := by
        unfold expectedApproxValue
        rw [← hT]; simp [hterm]
      unfold expectedTDError
      rw [hV, ← hT]; ring
    rw [if_neg h1]
    by_cases hn0 : n = 0
    · subst hn0
      rw [if_pos (by omega)]
      have hm : min (t + (0 + 1) - 1) (T - 1) = t := by omega
      rw [hm, Finset.Icc_self, Finset.sum_singleton, Finset.Ioc_self, Finset.prod_empty, mul_one]
      unfold expectedTDError; ring
    rw [if_neg (by omega)]
    have ih' := ih (t + 1) (by omega) (by omega)
    have e1 : t + 1 + n = t + (n + 1) := by omega
    rw [e1] at ih'
    rw [ih', tb257_sum_split _ _ t _ (by omega)]
    have hV : γ * ∑ a ∈ Finset.univ.erase (At (t + 1)), π.prob (St (t + 1)) a * Q (St (t + 1)) a
        + γ * π.prob (St (t + 1)) (At (t + 1)) * Q (St (t + 1)) (At (t + 1))
        = γ * expectedApproxValue π Q (St (t + 1)) := by
      unfold expectedApproxValue
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (At (t + 1)))]
      ring
    unfold expectedTDError
    linear_combination hV
