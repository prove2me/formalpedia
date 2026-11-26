-- Prove2me | solution 1 for QuarterSumLadder.weight_two_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:12:28.456418+00:00
-- url     : https://prove2.me/submissions/3411979b-904d-4571-91c7-eac309a89ffb

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Theorems.Thm_QuarterSumLadder_card_two_mod_four
public import Theorems.Thm_QuarterSumLadder_p_mul_c0
public import Theorems.Thm_QuarterSumLadder_p_mul_c1
public import Theorems.Thm_QuarterSumLadder_odd_card
public import Theorems.Thm_QuarterSumLadder_U_mod_eight
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_mod_eight_aux
public import Theorems.Thm_QuarterSumLadder_sum_univ_fibers
attribute [local simp] QuarterSumLadder.gi_im
attribute [local simp] QuarterSumLadder.gi_re



set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution :
    c0 χ ≡ 4 * (E χ 1 + E χ (-1)) [ZMOD 8] ∧ c1 χ ≡ 4 * (E χ gi + E χ (-gi)) [ZMOD 8] ∧
      c0 χ + c1 χ ≡ p - 1 [ZMOD 8] := by
  have hp1 : ((p : ℕ) : ZMod 8) = 1 := by
    rw [← ZMod.natCast_mod p 8, hp8]; simp
  have hc0 : ((c0 χ : ℤ) : ZMod 8) = ((U χ 1 - U χ (-1) : ℤ) : ZMod 8) := by
    rw [← p_mul_c0 hp8 hχ]; push_cast; rw [hp1, one_mul]
  have hc1 : ((c1 χ : ℤ) : ZMod 8) = ((U χ gi - U χ (-gi) : ℤ) : ZMod 8) := by
    rw [← p_mul_c1 hp8 hχ]; push_cast; rw [hp1, one_mul]
  have o1 := odd_card hp8 hχ (z := 1) (Or.inl rfl)
  have oi := odd_card hp8 hχ (z := gi) (Or.inr (Or.inl rfl))
  have om := odd_card hp8 hχ (z := -1) (Or.inr (Or.inr (Or.inl rfl)))
  have omi := odd_card hp8 hχ (z := -gi) (Or.inr (Or.inr (Or.inr rfl)))
  have e1 : ((((fiber χ 1).filter fun x => x.val % 2 = 1).card : ℕ) : ZMod 8) =
      (((fiber χ (-1)).filter fun x => x.val % 2 = 1).card : ℕ) := by
    congr 1; omega
  have e2 : ((((fiber χ gi).filter fun x => x.val % 2 = 1).card : ℕ) : ZMod 8) =
      (((fiber χ (-gi)).filter fun x => x.val % 2 = 1).card : ℕ) := by
    congr 1; omega
  have h8 : (8 : ZMod 8) = 0 := rfl
  -- the total count of `m ≡ 2 (mod 4)`
  have hE := sum_univ_fibers hχ (fun x : ZMod p => if x.val % 4 = 2 then (1 : ℕ) else 0)
    (by simp)
  simp only [← card_filter] at hE
  rw [card_two_mod_four hp8] at hE
  have hEq : (E χ 1 + E χ gi + E χ (-1) + E χ (-gi) : ℕ) = Q p := by
    unfold E; rw [hE]
  have hpq := mod_eight_aux hp8
  have hEq' : (E χ 1 : ZMod 8) + E χ gi + E χ (-1 : GaussianInt) + E χ (-gi) = Q p := by
    have := congrArg (fun n : ℕ => (n : ZMod 8)) hEq; push_cast at this; exact this
  have hQ : ((p : ℕ) : ZMod 8) - 1 = 4 * (Q p : ZMod 8) := by
    have : ((p - 1 : ℕ) : ZMod 8) = ((4 * Q p : ℕ) : ZMod 8) := by rw [hpq]
    push_cast [Nat.cast_sub hp.out.one_le] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · refine (ZMod.intCast_eq_intCast_iff _ _ 8).1 ?_
    rw [hc0]; push_cast
    rw [U_mod_eight (χ := χ), U_mod_eight (χ := χ), e1]
    linear_combination (-(E χ (-1) : ZMod 8)) * h8
  · refine (ZMod.intCast_eq_intCast_iff _ _ 8).1 ?_
    rw [hc1]; push_cast
    rw [U_mod_eight (χ := χ), U_mod_eight (χ := χ), e2]
    linear_combination (-(E χ (-gi) : ZMod 8)) * h8
  · refine (ZMod.intCast_eq_intCast_iff _ _ 8).1 ?_
    push_cast
    rw [hc0, hc1]; push_cast
    rw [U_mod_eight (χ := χ), U_mod_eight (χ := χ), U_mod_eight, U_mod_eight, e1, e2]
    linear_combination 4 * hEq' - hQ - ((E χ (-1) : ZMod 8) + E χ (-gi)) * h8
end QuarterSumLadder
