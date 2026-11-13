-- Prove2me | solution 1 for QFairEx.exists_cut_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-13T02:09:56.886877+00:00
-- url     : https://prove2.me/submissions/a39df871-c036-49d8-a73c-2576e8f35cad

import Mathlib

theorem solution (T : ℕ) (hT : 1 ≤ T) (p0 p1 : ℕ → ℝ) (h00 : p0 0 = 0) (h0T : p0 T = 1)
    (hodd : ∀ r, 1 ≤ r → r ≤ T → Odd r → p0 r = p0 (r - 1))
    (heven : ∀ r, 1 ≤ r → r ≤ T → Even r → p1 r = p1 (r - 1)) :
    ∃ t, t ≤ T ∧ 1 / (2 * (T : ℝ)) ≤ |p0 t - p1 t| := by
  by_contra hcon
  push Not at hcon
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  -- every increment of `p0` is strictly below `1 / T`
  have hstep : ∀ r, 1 ≤ r → r ≤ T → p0 r - p0 (r - 1) < 1 / (T : ℝ) := by
    intro r hr1 hrT
    rcases Nat.even_or_odd r with he | ho
    · have h1 := hcon r hrT
      have h2 := hcon (r - 1) (by omega)
      have h3 := heven r hr1 hrT he
      rw [abs_lt] at h1 h2
      have : (1 : ℝ) / T = 1 / (2 * T) + 1 / (2 * T) := by field_simp; ring
      rw [this]
      linarith [h1.1, h1.2, h2.1, h2.2]
    · rw [hodd r hr1 hrT ho, sub_self]
      positivity
  -- hence `p0 t < t / T` for `1 ≤ t ≤ T`
  have hsum : ∀ t, t ≤ T → p0 t ≤ t / (T : ℝ) ∧ (1 ≤ t → p0 t < t / (T : ℝ)) := by
    intro t
    induction t with
    | zero => intro _; simp [h00]
    | succ t ih =>
      intro ht
      have ih' := (ih (by omega)).1
      have hs := hstep (t + 1) (by omega) ht
      simp only [Nat.add_sub_cancel] at hs
      have : ((t + 1 : ℕ) : ℝ) / T = t / T + 1 / T := by push_cast; ring
      rw [this]
      exact ⟨by linarith, fun _ => by linarith⟩
  have := (hsum T le_rfl).2 hT
  rw [h0T, div_self hTpos.ne'] at this
  exact lt_irrefl _ this
