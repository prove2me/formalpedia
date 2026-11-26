-- Prove2me | solution 1 for P2M_QuadraticFloor_root_count__8bce20a9a3c2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:20.995625+00:00
-- url     : https://prove2.me/submissions/d30059cc-6853-4605-87b3-6785c723db7a

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount
public import Theorems.Thm_QuadraticFloor_sum_range_alt_odd
public import Theorems.Thm_QuadraticFloor_sum_range_even_odd
public import Theorems.Thm_QuadraticFloor_odd_of_ne_two
public import Theorems.Thm_QuadraticFloor_sum_range_eq_sum_zmod
public import Theorems.Thm_QuadraticFloor_negOnePow_ediv
public import Theorems.Thm_QuadraticFloor_even_sub_C
public import Theorems.Thm_QuadraticFloor_negOnePow_emod
public import Theorems.Thm_QuadraticFloor_card_quadratic_eq
public import Theorems.Thm_QuadraticFloor_sum_quadraticChar_affine

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) {A B : ℤ} (C : ℤ) (hAB : Even (A + B)) (hpA : ¬ (p : ℤ) ∣ A) :
    floorSum A B C p = (C.negOnePow : ℤ) *
      (1 + 2 * ∑ j ∈ range ((p + 1) / 2), legendreSym p (B ^ 2 - 4 * A * C + 8 * A * j)) := by
  set χ := quadraticChar (ZMod p)
  have hA : (A : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨m, hm⟩ := odd_of_ne_two hp2
  -- Step 1: each term is `(-1)^C (-1)^{⟨v⟩}`.
  have hterm : ∀ n : ℕ, (((A * n ^ 2 + B * n + C) / (p : ℤ)).negOnePow : ℤ) = (C.negOnePow : ℤ) *
      (-1) ^ (((A : ZMod p) * (n : ZMod p) ^ 2 + B * n + C)).val := by
    intro n
    rw [negOnePow_ediv hp2 _ C (even_sub_C hAB n C), negOnePow_emod]
    push_cast; rfl
  rw [floorSum, sum_congr rfl fun n _ => hterm n, ← mul_sum]
  congr 1
  -- Step 2: pass to `ZMod p` and group by the value.
  rw [sum_range_eq_sum_zmod (fun x : ZMod p => (-1 : ℤ) ^ ((A : ZMod p) * x ^ 2 + B * x + C).val)]
  rw [← sum_fiberwise univ (fun x : ZMod p => (A : ZMod p) * x ^ 2 + B * x + C)
    (fun x => (-1 : ℤ) ^ ((A : ZMod p) * x ^ 2 + B * x + C).val)]
  have hfib : ∀ y : ZMod p, ∑ x ∈ univ.filter (fun x : ZMod p => (A : ZMod p) * x ^ 2 + B * x + C = y),
      (-1 : ℤ) ^ ((A : ZMod p) * x ^ 2 + B * x + C).val =
      (-1) ^ y.val * (χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * y) + 1) := by
    intro y
    rw [sum_congr rfl fun x hx => by rw [(mem_filter.1 hx).2], sum_const, nsmul_eq_mul,
      card_quadratic_eq hp2 hA y]
    ring
  rw [sum_congr rfl fun y _ => hfib y]
  -- Step 3: back to `range p`, and split the alternating sign into even terms.
  rw [← sum_range_eq_sum_zmod (fun y : ZMod p =>
    (-1 : ℤ) ^ y.val * (χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * y) + 1))]
  have hval : ∀ r ∈ range p, (-1 : ℤ) ^ ((r : ZMod p)).val *
      (χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * (r : ZMod p)) + 1) =
      2 * (if Even r then χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * (r : ZMod p)) else 0) -
        χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * (r : ZMod p)) + (-1) ^ r := by
    intro r hr
    rw [ZMod.val_cast_of_lt (mem_range.1 hr)]
    rcases Nat.even_or_odd r with h | h
    · simp only [h, ite_true, h.neg_one_pow]; ring
    · simp only [Nat.not_even_iff_odd.2 h, ite_false, h.neg_one_pow]; ring
  rw [sum_congr rfl hval, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  have hfull : ∑ r ∈ range p, χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * (r : ZMod p)) = 0 := by
    rw [sum_range_eq_sum_zmod (fun y : ZMod p => χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * y))]
    have h4A : (4 * A : ZMod p) ≠ 0 := by
      have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
      rw [show (4 : ZMod p) * A = 2 * (2 * A) by ring]; exact mul_ne_zero h2 (mul_ne_zero h2 hA)
    exact sum_quadraticChar_affine hp2 h4A _
  rw [hfull, show range p = range (2 * m + 1) by rw [hm], sum_range_alt_odd, sum_range_even_odd,
    show (p + 1) / 2 = m + 1 by omega]
  have hleg : ∀ j : ℕ, χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * ((2 * j : ℕ) : ZMod p)) =
      legendreSym p (B ^ 2 - 4 * A * C + 8 * A * j) := by
    intro j
    simp only [legendreSym, χ]
    push_cast; ring_nf
  rw [sum_congr rfl fun j _ => hleg j]
  ring
end QuadraticFloor
