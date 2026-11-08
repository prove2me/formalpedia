-- Prove2me | solution 1 for Sherbrooke.cond12_optimal
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:59:28.757022+00:00
-- url     : https://prove2.me/submissions/bda975c6-1f50-4028-9efc-ab666acf19de

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull
import Definitions.Def_Sherbrooke_Cond12

open Sherbrooke in
theorem solution (c : ℝ) (Ξ : ℕ → ℝ) (hanti : Antitone Ξ)
    (hbdd : BddBelow (Set.range Ξ)) (mbar : ℕ) (h12 : Cond12 c Ξ mbar) :
    ∀ k : ℕ, c * (mbar : ℝ) + Ξ mbar ≤ c * (k : ℝ) + Ξ k := by
  obtain ⟨L, hL⟩ := hbdd
  have hL' : ∀ k, L ≤ Ξ k := fun k => hL ⟨k, rfl⟩
  set H := lowerHull Ξ with hH
  have hHdef : ∀ m, H m = sSup {y : ℝ | ∃ a b : ℝ, (∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) ∧
      y = a * (m : ℝ) + b} := fun m => rfl
  have hne : ∀ m : ℕ, ({y : ℝ | ∃ a b : ℝ, (∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) ∧
      y = a * (m : ℝ) + b}).Nonempty :=
    fun m => ⟨L, 0, L, fun k => by simp [hL' k], by simp⟩
  have hbd : ∀ m : ℕ, BddAbove {y : ℝ | ∃ a b : ℝ, (∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) ∧
      y = a * (m : ℝ) + b} :=
    fun m => ⟨Ξ m, by rintro y ⟨a, b, h, rfl⟩; exact h m⟩
  have hle : ∀ a b : ℝ, (∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) → ∀ m : ℕ, a * (m : ℝ) + b ≤ H m :=
    fun a b h m => by rw [hHdef]; exact le_csSup (hbd m) ⟨a, b, h, rfl⟩
  have hHΞ : ∀ m, H m ≤ Ξ m := by
    intro m; rw [hHdef]; exact csSup_le (hne m) (by rintro y ⟨a, b, h, rfl⟩; exact h m)
  have hmid : ∀ m : ℕ, 2 * H (m + 1) ≤ H m + H (m + 2) := by
    intro m
    have : H (m + 1) ≤ (H m + H (m + 2)) / 2 := by
      rw [hHdef (m + 1)]
      apply csSup_le (hne _)
      rintro y ⟨a, b, h, rfl⟩
      have h1 := hle a b h m
      have h2 := hle a b h (m + 2)
      push_cast at h1 h2 ⊢
      linarith
    linarith
  set d : ℕ → ℝ := fun m => H (m + 1) - H m with hd
  have hdmono : Monotone d := by
    apply monotone_nat_of_le_succ
    intro m
    simp only [hd]
    have := hmid m
    rw [show m + 1 + 1 = m + 2 by ring]
    linarith
  have hright : ∀ j : ℕ, H mbar + j * d mbar ≤ H (mbar + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hdj : d mbar ≤ d (mbar + j) := hdmono (by omega)
      have e : H (mbar + (j + 1)) = H (mbar + j) + d (mbar + j) := by
        simp only [hd]; rw [show mbar + j + 1 = mbar + (j + 1) by ring]; ring
      rw [e]; push_cast; nlinarith
  have hleft : 1 ≤ mbar → ∀ j : ℕ, j ≤ mbar → H mbar - j * d (mbar - 1) ≤ H (mbar - j) := by
    intro hm j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have hdj : d (mbar - (j + 1)) ≤ d (mbar - 1) := hdmono (by omega)
      have e : H (mbar - j) = H (mbar - (j + 1)) + d (mbar - (j + 1)) := by
        simp only [hd]; rw [show mbar - (j + 1) + 1 = mbar - j by omega]; ring
      push_cast
      linarith
  obtain ⟨hplus, hminus⟩ := h12
  have hplus' : -c ≤ d mbar := by simp only [hd]; linarith
  have hD : 1 ≤ mbar → d (mbar - 1) < -c := by
    intro hm1
    rcases hminus with h0 | hm
    · omega
    · simp only [hd]
      rw [show mbar - 1 + 1 = mbar by omega]
      linarith
  -- equality of hull and sequence at mbar
  have hEq : H mbar = Ξ mbar := by
    apply le_antisymm (hHΞ mbar)
    rcases Nat.eq_zero_or_pos mbar with h0 | hm1
    · rw [h0]
      have hmin : ∀ k : ℕ, (L - Ξ 0) * (k : ℝ) + Ξ 0 ≤ Ξ k := by
        intro k
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simp
        · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
          have h0' : L - Ξ 0 ≤ 0 := by linarith [hL' 0]
          nlinarith [hL' k]
      have := hle _ _ hmin 0
      simpa using this
    · by_contra hlt
      push_neg at hlt
      have hminus' := hD hm1
      set s' := (d (mbar - 1) + -c) / 2 with hs'
      set e2 := (-c - d (mbar - 1)) / 2 with he2
      have he2pos : 0 < e2 := by rw [he2]; linarith
      set e1 := Ξ mbar - H mbar with he1
      have he1pos : 0 < e1 := by rw [he1]; linarith
      set ε := min e1 e2 with hε
      have hεpos : 0 < ε := lt_min he1pos he2pos
      have hε1 : ε ≤ e1 := min_le_left _ _
      have hε2 : ε ≤ e2 := min_le_right _ _
      have hmin : ∀ k : ℕ, s' * (k : ℝ) + (H mbar - s' * mbar + ε) ≤ Ξ k := by
        intro k
        rcases lt_trichotomy k mbar with hk | hk | hk
        · have hj := hleft hm1 (mbar - k) (by omega)
          rw [show mbar - (mbar - k) = k by omega] at hj
          have hcast : ((mbar - k : ℕ) : ℝ) = (mbar : ℝ) - k := by
            rw [Nat.cast_sub hk.le]
          rw [hcast] at hj
          have hj1 : (1 : ℝ) ≤ (mbar : ℝ) - k := by
            have : ((k + 1 : ℕ) : ℝ) ≤ mbar := by exact_mod_cast hk
            push_cast at this; linarith
          have := hHΞ k
          have hrel : s' - d (mbar - 1) = e2 := by rw [hs', he2]; ring
          nlinarith
        · subst hk
          linarith
        · have hj := hright (k - mbar)
          rw [show mbar + (k - mbar) = k by omega] at hj
          have hcast : ((k - mbar : ℕ) : ℝ) = (k : ℝ) - mbar := by
            rw [Nat.cast_sub hk.le]
          rw [hcast] at hj
          have hj1 : (1 : ℝ) ≤ (k : ℝ) - mbar := by
            have : ((mbar + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
            push_cast at this; linarith
          have := hHΞ k
          have hrel : s' = -c - e2 := by rw [hs', he2]; ring
          nlinarith
      have := hle _ _ hmin mbar
      linarith
  intro k
  rw [← hEq]
  have hk := hHΞ k
  rcases le_or_gt mbar k with hmk | hkm
  · have hj := hright (k - mbar)
    rw [show mbar + (k - mbar) = k by omega] at hj
    have hcast : ((k - mbar : ℕ) : ℝ) = (k : ℝ) - mbar := by rw [Nat.cast_sub hmk]
    rw [hcast] at hj
    have hnn : (0 : ℝ) ≤ (k : ℝ) - mbar := by
      have : (mbar : ℝ) ≤ k := by exact_mod_cast hmk
      linarith
    nlinarith
  · have hm1 : 1 ≤ mbar := by omega
    have hj := hleft hm1 (mbar - k) (by omega)
    rw [show mbar - (mbar - k) = k by omega] at hj
    have hcast : ((mbar - k : ℕ) : ℝ) = (mbar : ℝ) - k := by rw [Nat.cast_sub hkm.le]
    rw [hcast] at hj
    have hnn : (0 : ℝ) ≤ (mbar : ℝ) - k := by
      have : (k : ℝ) ≤ mbar := by exact_mod_cast hkm.le
      linarith
    have := hD hm1
    nlinarith
