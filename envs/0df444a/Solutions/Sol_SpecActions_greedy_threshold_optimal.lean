-- Prove2me | solution 1 for SpecActions.greedy_threshold_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-12T04:18:59.466236+00:00
-- url     : https://prove2.me/submissions/b4d443f1-d430-4819-89f6-381d1815b29c

import Mathlib
import Definitions.Def_SpecActions_model

open Finset SpecActions

/-- One step of the per-window objective: launching one more branch changes the
objective by exactly `Δ · δq(j) - c`. -/
private theorem obj_step (pv : ℕ → ℝ) (Δ c : ℝ) (j : ℕ) :
    specObjective pv Δ c (j + 1)
      = specObjective pv Δ c j + (Δ * dqhit pv j - c) := by
  unfold specObjective qhit dqhit
  rw [Finset.prod_range_succ]
  push_cast
  ring

theorem solution (pv : ℕ → ℝ) (Δ c : ℝ) (k : ℕ)
    (hΔ : 0 < Δ) (hc : 0 < c)
    (hpv0 : ∀ j, 0 ≤ pv j) (hpv1 : ∀ j, pv j ≤ 1)
    (hsorted : ∀ i j, i ≤ j → pv j ≤ pv i)
    (m : ℕ) (hm : m ≤ k)
    (hbelow : ∀ j < m, c ≤ Δ * dqhit pv j)
    (habove : ∀ j, m ≤ j → Δ * dqhit pv j ≤ c) :
    ∀ n ≤ k, specObjective pv Δ c n ≤ specObjective pv Δ c m := by
  have up : ∀ b, b ≤ m → ∀ a, a ≤ b → specObjective pv Δ c a ≤ specObjective pv Δ c b := by
    intro b
    induction b with
    | zero => intro _ a ha; simp only [Nat.le_zero] at ha; subst ha; exact le_refl _
    | succ b ih =>
      intro hb a ha
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · have hab : a ≤ b := by omega
        have h1 := ih (by omega) a hab
        have h2 : specObjective pv Δ c b ≤ specObjective pv Δ c (b + 1) := by
          rw [obj_step]
          have := hbelow b (by omega)
          linarith
        linarith
      · have : a = b + 1 := by omega
        subst this; exact le_refl _
  have down : ∀ a, m ≤ a → specObjective pv Δ c a ≤ specObjective pv Δ c m := by
    intro a
    induction a with
    | zero => intro h; simp only [Nat.le_zero] at h; subst h; exact le_refl _
    | succ a ih =>
      intro ha
      rcases Nat.lt_or_ge m (a + 1) with h | h
      · have hma : m ≤ a := by omega
        have h1 := ih hma
        have h2 : specObjective pv Δ c (a + 1) ≤ specObjective pv Δ c a := by
          rw [obj_step]
          have := habove a hma
          linarith
        linarith
      · have : m = a + 1 := by omega
        subst this; exact le_refl _
  intro n _
  rcases Nat.le_total n m with h | h
  · exact up m (le_refl _) n h
  · exact down n h
