-- Prove2me | solution 1 for Sherbrooke.lowerHull_secant_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:43:17.8885+00:00
-- url     : https://prove2.me/submissions/e7034dac-b6af-4fa7-b3c2-0da984161baa

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull

namespace Aux_Sherbrooke_secant
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

lemma kink_eq (Ξ : ℕ → ℝ) (hbdd : BddBelow (Set.range Ξ)) (m : ℕ) (hm : 0 < m)
    (hs12' : lowerHull Ξ m - lowerHull Ξ (m - 1) < lowerHull Ξ (m + 1) - lowerHull Ξ m) :
    lowerHull Ξ m = Ξ m := by
  apply le_antisymm (hull_le Ξ hbdd m)
  by_contra hlt
  push_neg at hlt
  set s1 := lowerHull Ξ m - lowerHull Ξ (m - 1) with hs1
  set s2 := lowerHull Ξ (m + 1) - lowerHull Ξ m with hs2
  have hs12 : s1 < s2 := by rw [hs1, hs2]; exact hs12'
  set ε := Ξ m - lowerHull Ξ m with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set t := (s1 + s2) / 2 with ht
  set δ := min ε ((s2 - s1) / 2) with hδ
  have hδpos : 0 < δ := lt_min hεpos (by linarith)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδs : δ ≤ (s2 - s1) / 2 := min_le_right _ _
  have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hline : ∀ k : ℕ, t * (k : ℝ) + (lowerHull Ξ m + δ - t * m) ≤ Ξ k := by
    intro k
    rcases lt_trichotomy k m with hk | hk | hk
    · -- k < m
      have hconv := hull_convex Ξ hbdd k (m - 1) m (by omega) (by omega)
      rw [hm1] at hconv
      have hkm : (k : ℝ) + 1 ≤ m := by exact_mod_cast hk
      have hhk : lowerHull Ξ m - ((m : ℝ) - k) * s1 ≤ lowerHull Ξ k := by
        rw [hs1]; nlinarith
      have := hull_le Ξ hbdd k
      have h5 : δ ≤ (t - s1) * ((m : ℝ) - k) := by
        have : (t - s1) * 1 ≤ (t - s1) * ((m : ℝ) - k) :=
          mul_le_mul_of_nonneg_left (by linarith) (by rw [ht]; linarith)
        rw [ht] at this ⊢; linarith
      nlinarith
    · subst hk; linarith
    · have hconv := hull_convex Ξ hbdd m (m + 1) k (by omega) (by omega)
      have hkm : (m : ℝ) + 1 ≤ k := by exact_mod_cast hk
      push_cast at hconv
      have hhk : lowerHull Ξ m + ((k : ℝ) - m) * s2 ≤ lowerHull Ξ k := by
        rw [hs2]; nlinarith
      have := hull_le Ξ hbdd k
      have h5 : δ ≤ (s2 - t) * ((k : ℝ) - m) := by
        have : (s2 - t) * 1 ≤ (s2 - t) * ((k : ℝ) - m) :=
          mul_le_mul_of_nonneg_left (by linarith) (by rw [ht]; linarith)
        rw [ht] at this ⊢; linarith
      nlinarith
  have := line_le_hull Ξ t (lowerHull Ξ m + δ - t * m) hline m
  linarith

end Aux_Sherbrooke_secant

open Sherbrooke Aux_Sherbrooke_secant in
theorem solution (Ξ : ℕ → ℝ) (hanti : Antitone Ξ)
    (hbdd : BddBelow (Set.range Ξ)) (m : ℕ) (hlt : lowerHull Ξ m < Ξ m) :
    1 ≤ m ∧ lowerHull Ξ (m + 1) - lowerHull Ξ m = lowerHull Ξ m - lowerHull Ξ (m - 1) := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; rw [hull_zero Ξ hbdd] at hlt; exact absurd hlt (lt_irrefl _)
    · exact h
  refine ⟨hm, ?_⟩
  have hconv := hull_convex Ξ hbdd (m - 1) m (m + 1) (by omega) (by omega)
  have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm]; simp
  rw [hm1] at hconv
  push_cast at hconv
  have hle : lowerHull Ξ m - lowerHull Ξ (m - 1) ≤ lowerHull Ξ (m + 1) - lowerHull Ξ m := by
    nlinarith
  rcases eq_or_lt_of_le hle with heq | hlt'
  · exact heq.symm
  · exfalso
    have := kink_eq Ξ hbdd m hm hlt'
    linarith
