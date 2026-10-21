-- Prove2me | solution 1 for ShapeMoment.LogConcave.geometric_of_tight
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:48:44.014989+00:00
-- url     : https://prove2.me/submissions/df136825-c47d-444e-9013-89c0109ee591

import Mathlib
set_option autoImplicit false

theorem solution (x : ℕ → ℝ) (u v : ℕ) (huv : u ≤ v)
    (hpos : ∀ j, u ≤ j → j ≤ v → 0 < x j)
    (htight : ∀ j, u < j → j < v → x (j - 1) * x (j + 1) = x j ^ 2) :
    ∃ r : ℝ, 0 < r ∧ ∀ j, u ≤ j → j ≤ v → x j = x u * r ^ (j - u) := by
  have hu : 0 < x u := hpos u le_rfl huv
  by_cases h : u < v
  · refine ⟨x (u + 1) / x u, div_pos (hpos _ (by omega) (by omega)) hu, ?_⟩
    set r := x (u + 1) / x u with hr
    have hr' : x (u + 1) = x u * r := by rw [hr]; field_simp
    -- two-step induction
    have key : ∀ k, k + 1 ≤ v - u → x (u + k) = x u * r ^ k ∧ x (u + k + 1) = x u * r ^ (k + 1) := by
      intro k
      induction k with
      | zero => intro _; simp [hr']
      | succ k ih =>
        intro hk
        obtain ⟨h1, h2⟩ := ih (by omega)
        refine ⟨by rw [← add_assoc]; exact h2, ?_⟩
        by_cases hk2 : k + 2 ≤ v - u
        · have ht := htight (u + k + 1) (by omega) (by omega)
          have e1 : u + k + 1 - 1 = u + k := by omega
          rw [e1, h1, h2] at ht
          have hp := hpos (u + k + 1) (by omega) (by omega)
          rw [h2] at hp
          have hxr : 0 < x u * r ^ (k + 1) := hp
          have : x (u + k + 1 + 1) = x u * r ^ (k + 2) := by
            have hne : x u * r ^ (k + 1) ≠ 0 := hxr.ne'
            apply mul_left_cancel₀ hne
            calc x u * r ^ (k + 1) * x (u + k + 1 + 1) = x u * r ^ k * x (u + k + 1 + 1) * r := by ring
              _ = _ := by rw [ht]; ring
          have e : u + (k + 1) + 1 = u + k + 1 + 1 := by omega
          rw [e, this]
        · omega
    intro j hj1 hj2
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj1
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      have := (key m (by omega)).2
      have e : u + (m + 1) - u = m + 1 := by omega
      rw [Nat.succ_eq_add_one, e]
      exact this
  · have : v = u := by omega
    subst this
    refine ⟨1, one_pos, ?_⟩
    intro j h1 h2
    have : j = v := by omega
    subst this
    simp
