-- Prove2me | solution 1 for QuadraticFloor.floorSum_five_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:54.214678+00:00
-- url     : https://prove2.me/submissions/f61299ca-d302-459f-ba52-951e9194797c

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
public import Theorems.Thm_QuadraticFloor_sum_modEq_card
public import Theorems.Thm_QuadraticFloor_card_zero_terms
public import Theorems.Thm_P2M_QuadraticFloor_root_count__8bce20a9a3c2


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (hp5 : p ≠ 5) {B : ℤ} (hB : Odd B) :
    floorSum 5 B 0 p - 1 ≡ 2 * (((p + 1) / 2 : ℕ) - zB B p) [ZMOD 4] := by
  have hpA : ¬ (p : ℤ) ∣ 5 := by
    intro h
    have : p ∣ 5 := by exact_mod_cast h
    exact hp5 ((Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).1 this)
  have hAB : Even ((5 : ℤ) + B) := (by decide : Odd (5 : ℤ)).add_odd hB
  rw [root_count' hp2 0 hAB hpA, Int.negOnePow_zero, Units.val_one, one_mul, add_sub_cancel_left]
  have hs : ∑ j ∈ range ((p + 1) / 2), legendreSym p (B ^ 2 - 4 * 5 * 0 + 8 * 5 * j) =
      ∑ j ∈ range ((p + 1) / 2), legendreSym p (B ^ 2 + 40 * (j : ℤ)) :=
    sum_congr rfl fun j _ => by ring_nf
  rw [hs]
  have hmod := sum_modEq_card (s := range ((p + 1) / 2))
    (f := fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ))) (fun j _ => by
      by_cases h0 : legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0
      · left; exact h0
      · right
        exact legendreSym.eq_one_or_neg_one p (fun h => h0 ((legendreSym.eq_zero_iff p _).2 h)))
  have hcard := card_filter_add_card_filter_not (s := range ((p + 1) / 2))
    (fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0)
  rw [card_range] at hcard
  have hz := card_zero_terms hp2 hp5 B
  have hne : ((range ((p + 1) / 2)).filter fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ)) ≠ 0).card =
      (p + 1) / 2 - ((range ((p + 1) / 2)).filter
        fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0).card := by
    simp only [ne_eq]; omega
  rw [hne] at hmod
  have hle := card_filter_le (range ((p + 1) / 2)) (fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0)
  rw [card_range] at hle
  rw [Nat.cast_sub hle, hz] at hmod
  have := Int.ModEq.mul_left' (c := 2) hmod
  rw [show (2 : ℤ) * 2 = 4 by norm_num] at this
  exact this
end QuadraticFloor
