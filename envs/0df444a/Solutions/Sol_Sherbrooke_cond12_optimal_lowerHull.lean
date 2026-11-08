-- Prove2me | solution 1 for Sherbrooke.cond12_optimal_lowerHull
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:19:34.056799+00:00
-- url     : https://prove2.me/submissions/951dddb5-da65-4c1d-9276-167b0b6d6eaf

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull
import Definitions.Def_Sherbrooke_Cond12

namespace Aux_Sherbrooke_c12opt
open Sherbrooke

lemma hull_nonempty (Ξ : ℕ → ℝ) (hbdd : BddBelow (Set.range Ξ)) (m : ℕ) :
    {y : ℝ | ∃ a b : ℝ, (∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) ∧ y = a * (m : ℝ) + b}.Nonempty := by
  obtain ⟨L0, hL0⟩ := hbdd
  refine ⟨0 * (m : ℝ) + L0, 0, L0, fun k => ?_, rfl⟩
  rw [zero_mul, zero_add]; exact hL0 ⟨k, rfl⟩

lemma hull_bdd (Ξ : ℕ → ℝ) (m : ℕ) :
    BddAbove {y : ℝ | ∃ a b : ℝ, (∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) ∧ y = a * (m : ℝ) + b} := by
  refine ⟨Ξ m, ?_⟩
  rintro y ⟨a, b, hab, rfl⟩
  exact hab m

lemma line_le_hull (Ξ : ℕ → ℝ) (a b : ℝ) (hab : ∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) (m : ℕ) :
    a * (m : ℝ) + b ≤ lowerHull Ξ m :=
  le_csSup (hull_bdd Ξ m) ⟨a, b, hab, rfl⟩

lemma hull_le (Ξ : ℕ → ℝ) (hbdd : BddBelow (Set.range Ξ)) (m : ℕ) : lowerHull Ξ m ≤ Ξ m := by
  apply csSup_le (hull_nonempty Ξ hbdd m)
  rintro y ⟨a, b, hab, rfl⟩
  exact hab m

lemma hull_convex (Ξ : ℕ → ℝ) (hbdd : BddBelow (Set.range Ξ)) (p j q : ℕ) (hpj : p ≤ j)
    (hjq : j ≤ q) :
    ((q : ℝ) - p) * lowerHull Ξ j ≤ ((q : ℝ) - j) * lowerHull Ξ p + ((j : ℝ) - p) * lowerHull Ξ q := by
  have hpj' : (p : ℝ) ≤ j := by exact_mod_cast hpj
  have hjq' : (j : ℝ) ≤ q := by exact_mod_cast hjq
  rcases Nat.eq_or_lt_of_le (le_trans hpj hjq) with hpq | hpq
  · obtain rfl : j = p := by omega
    obtain rfl : q = j := by omega
    simp
  have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
  have hpos : 0 < (q : ℝ) - p := by linarith [hpq']
  have key : lowerHull Ξ j ≤ (((q : ℝ) - j) * lowerHull Ξ p + ((j : ℝ) - p) * lowerHull Ξ q)
      / ((q : ℝ) - p) := by
    apply csSup_le (hull_nonempty Ξ hbdd j)
    rintro y ⟨a, b, hab, rfl⟩
    rw [le_div_iff₀ hpos]
    have h1 := line_le_hull Ξ a b hab p
    have h2 := line_le_hull Ξ a b hab q
    have e : (a * (j : ℝ) + b) * ((q : ℝ) - p)
        = ((q : ℝ) - j) * (a * p + b) + ((j : ℝ) - p) * (a * q + b) := by ring
    rw [e]
    have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ (q : ℝ) - j)
    have h4 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ (j : ℝ) - p)
    linarith
  rw [le_div_iff₀ hpos] at key
  linarith

lemma hull_zero (Ξ : ℕ → ℝ) (hbdd : BddBelow (Set.range Ξ)) : lowerHull Ξ 0 = Ξ 0 := by
  apply le_antisymm (hull_le Ξ hbdd 0)
  obtain ⟨L0, hL0⟩ := hbdd
  have hL : ∀ k, L0 ≤ Ξ k := fun k => hL0 ⟨k, rfl⟩
  have := line_le_hull Ξ (L0 - Ξ 0) (Ξ 0) (fun k => by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have h0 : L0 - Ξ 0 ≤ 0 := by linarith [hL 0]
      have : (L0 - Ξ 0) * (k : ℝ) ≤ (L0 - Ξ 0) * 1 := mul_le_mul_of_nonpos_left hk1 h0
      linarith [hL k]) 0
  simpa using this

end Aux_Sherbrooke_c12opt

open Sherbrooke Aux_Sherbrooke_c12opt in
theorem solution (c : ℝ) (Ξ : ℕ → ℝ) (hbdd : BddBelow (Set.range Ξ))
    (mbar : ℕ) (h12 : Cond12 c Ξ mbar) :
    ∀ k : ℕ, c * (mbar : ℝ) + lowerHull Ξ mbar ≤ c * (k : ℝ) + lowerHull Ξ k := by
  obtain ⟨hc1, hc2⟩ := h12
  intro k
  rcases lt_trichotomy k mbar with hk | hk | hk
  · -- k < mbar, so mbar > 0
    rcases hc2 with hm | hc2
    · omega
    have hconv := hull_convex Ξ hbdd k (mbar - 1) mbar (by omega) (by omega)
    have hm1 : ((mbar - 1 : ℕ) : ℝ) = (mbar : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hm1] at hconv
    have hkm : (k : ℝ) + 1 ≤ mbar := by exact_mod_cast hk
    have hd : 0 ≤ (mbar : ℝ) - k := by linarith
    have h1 : (lowerHull Ξ mbar - lowerHull Ξ (mbar - 1)) * ((mbar : ℝ) - k)
        ≤ (-c) * ((mbar : ℝ) - k) := mul_le_mul_of_nonneg_right (by linarith) hd
    nlinarith
  · subst hk; exact le_rfl
  · have hconv := hull_convex Ξ hbdd mbar (mbar + 1) k (by omega) (by omega)
    push_cast at hconv
    have hkm : (mbar : ℝ) + 1 ≤ k := by exact_mod_cast hk
    have hd : 0 ≤ (k : ℝ) - mbar := by linarith
    have h1 : (-c) * ((k : ℝ) - mbar)
        ≤ (lowerHull Ξ (mbar + 1) - lowerHull Ξ mbar) * ((k : ℝ) - mbar) :=
      mul_le_mul_of_nonneg_right (by linarith) hd
    nlinarith
