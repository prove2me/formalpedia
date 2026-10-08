-- Prove2me | solution 1 for SuttonBartoRL.NStep.controlVariateReturn_eq_sum_tdError
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:02:05.904419+00:00
-- url     : https://prove2.me/submissions/ae2a9ce6-ebdf-4570-a389-866f80d50878

import Mathlib
import Definitions.Def_SuttonBartoRL_NStep_EpisodeReturns

namespace SuttonBartoRL.NStep

theorem a0129657_aux {S A : Type} [Fintype A] (π b : Policy S A)
    (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (At : ℕ → A) (V : S → ℝ) (h : ℕ) :
    ∀ d t : ℕ, t + d = h →
    controlVariateReturn π b γ R St At V t h - V (St t) =
      ∑ k ∈ Finset.Ico t h,
        γ ^ (k - t) * (∏ i ∈ Finset.Icc t k, isRatio π b St At i) * tdError γ R St V k := by
  intro d
  induction d with
  | zero =>
    intro t ht
    subst ht
    rw [controlVariateReturn]
    simp
  | succ d ih =>
    intro t ht
    have hlt : t < h := by omega
    have ih' := ih (t + 1) (by omega)
    rw [controlVariateReturn, if_pos hlt, Finset.sum_eq_sum_Ico_succ_bot hlt]
    have hsum : ∑ k ∈ Finset.Ico (t + 1) h,
        γ ^ (k - t) * (∏ i ∈ Finset.Icc t k, isRatio π b St At i) * tdError γ R St V k
        = isRatio π b St At t * γ * ∑ k ∈ Finset.Ico (t + 1) h,
        γ ^ (k - (t + 1)) * (∏ i ∈ Finset.Icc (t + 1) k, isRatio π b St At i) *
          tdError γ R St V k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk1 : k - t = (k - (t + 1)) + 1 := by omega
      rw [hk1, pow_succ, ← Finset.insert_Icc_add_one_left_eq_Icc (by omega : t ≤ k),
        Finset.prod_insert (by simp)]
      ring
    rw [hsum, ← ih']
    simp [tdError]
    ring

end SuttonBartoRL.NStep

open SuttonBartoRL.NStep in
theorem solution {S A : Type} [Fintype A] (π b : Policy S A)
    (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (At : ℕ → A) (V : S → ℝ) (t h : ℕ) (hth : t ≤ h) :
    controlVariateReturn π b γ R St At V t h - V (St t) =
      ∑ k ∈ Finset.Ico t h,
        γ ^ (k - t) * (∏ i ∈ Finset.Icc t k, isRatio π b St At i) * tdError γ R St V k := by
  exact a0129657_aux π b γ R St At V h (h - t) t (by omega)
