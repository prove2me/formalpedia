-- Prove2me | solution 1 for QuarterSumLadder.comparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:16:01.88764+00:00
-- url     : https://prove2.me/submissions/07486a34-b5bb-4dc8-904d-8099ac7a4d3a

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary
public import Theorems.Thm_QuarterSumLadder_card_mod_eight
public import Theorems.Thm_QuarterSumLadder_U_mod_sixteen
public import Theorems.Thm_QuarterSumLadder_E_add_R
public import Theorems.Thm_QuarterSumLadder_R_one
public import Theorems.Thm_QuarterSumLadder_R_three
public import Theorems.Thm_QuarterSumLadder_R_two
public import Theorems.Thm_QuarterSumLadder_R_zero
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_odd_card
public import Theorems.Thm_QuarterSumLadder_p_mul_c0
public import Theorems.Thm_QuarterSumLadder_p_mul_c1
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
    (p : ℤ) * (c0 χ - c1 χ) ≡ -4 * ((Omega χ).re - (Omega χ).im) [ZMOD 16] := by
  refine (ZMod.intCast_eq_intCast_iff _ _ 16).1 ?_
  have hpc : (p : ℤ) * (c0 χ - c1 χ) = (U χ 1 - U χ (-1)) - (U χ gi - U χ (-gi)) := by
    rw [mul_sub, p_mul_c0 hp8 hχ, p_mul_c1 hp8 hχ]
  rw [hpc]; push_cast
  rw [U_mod_sixteen (χ := χ), U_mod_sixteen (χ := χ), U_mod_sixteen (χ := χ),
    U_mod_sixteen (χ := χ)]
  -- odd counts agree
  have o1 := odd_card hp8 hχ (z := 1) (Or.inl rfl)
  have oi := odd_card hp8 hχ (z := gi) (Or.inr (Or.inl rfl))
  have om := odd_card hp8 hχ (z := -1) (Or.inr (Or.inr (Or.inl rfl)))
  have omi := odd_card hp8 hχ (z := -gi) (Or.inr (Or.inr (Or.inr rfl)))
  have e1 : ((((fiber χ 1).filter fun x => x.val % 2 = 1).card : ℕ) : ZMod 16) =
      (((fiber χ (-1)).filter fun x => x.val % 2 = 1).card : ℕ) := by congr 1; omega
  have e2 : ((((fiber χ gi).filter fun x => x.val % 2 = 1).card : ℕ) : ZMod 16) =
      (((fiber χ (-1)).filter fun x => x.val % 2 = 1).card : ℕ) := by congr 1; omega
  have e3 : ((((fiber χ (-gi)).filter fun x => x.val % 2 = 1).card : ℕ) : ZMod 16) =
      (((fiber χ (-1)).filter fun x => x.val % 2 = 1).card : ℕ) := by congr 1; omega
  rw [e1, e2, e3]
  -- the counts of `m ≡ ±3 (mod 8)`
  have hT := sum_univ_fibers hχ
    (fun x : ZMod p => if x.val % 8 = 3 ∨ x.val % 8 = 5 then (1 : ℕ) else 0) (by simp)
  simp only [← card_filter] at hT
  have h35 : (univ.filter fun x : ZMod p => x.val % 8 = 3 ∨ x.val % 8 = 5).card =
      2 * ((p - 1) / 8) := by
    rw [filter_or, card_union_of_disjoint (disjoint_filter.2 fun x _ h3 h5 => by omega),
      card_mod_eight hp8 (r := 3) (by norm_num) (by norm_num),
      card_mod_eight hp8 (r := 5) (by norm_num) (by norm_num)]
    ring
  rw [h35] at hT
  set T1 := ((fiber χ 1).filter fun x => x.val % 8 = 3 ∨ x.val % 8 = 5).card
  set Ti := ((fiber χ gi).filter fun x => x.val % 8 = 3 ∨ x.val % 8 = 5).card
  set Tm := ((fiber χ (-1)).filter fun x => x.val % 8 = 3 ∨ x.val % 8 = 5).card
  set Tmi := ((fiber χ (-gi)).filter fun x => x.val % 8 = 3 ∨ x.val % 8 = 5).card
  have hT' : (T1 : ZMod 16) + Ti + Tm + Tmi = 2 * (((p - 1) / 8 : ℕ) : ZMod 16) := by
    have := congrArg (fun n : ℕ => (n : ZMod 16)) hT; push_cast at this; exact this.symm
  -- `E_z = Q/2 - R(z)`
  have a := E_add_R hp8 hχ (z := 1) (Or.inl rfl)
  have b := E_add_R hp8 hχ (z := gi) (Or.inr (Or.inl rfl))
  have c := E_add_R hp8 hχ (z := -1) (Or.inr (Or.inr (Or.inl rfl)))
  have d := E_add_R hp8 hχ (z := -gi) (Or.inr (Or.inr (Or.inr rfl)))
  rw [← R_zero] at a; rw [← R_one] at b; rw [← R_two] at c; rw [← R_three] at d
  have hE : (E χ 1 : ZMod 16) - E χ (-1) - (E χ gi - E χ (-gi)) =
      -((R χ 0 : ZMod 16) - R χ 2 - (R χ 1 - R χ 3)) := by
    have a' := congrArg (fun n : ℕ => (n : ZMod 16)) a
    have b' := congrArg (fun n : ℕ => (n : ZMod 16)) b
    have c' := congrArg (fun n : ℕ => (n : ZMod 16)) c
    have d' := congrArg (fun n : ℕ => (n : ZMod 16)) d
    push_cast at a' b' c' d'
    linear_combination a' - c' - b' + d'
  have hre : ((Omega χ).re : ZMod 16) = (R χ 0 : ZMod 16) - R χ 2 := by
    show (((R χ 0 : ℤ) - R χ 2 : ℤ) : ZMod 16) = _; push_cast; ring
  have him : ((Omega χ).im : ZMod 16) = (R χ 1 : ZMod 16) - R χ 3 := by
    show (((R χ 1 : ℤ) - R χ 3 : ℤ) : ZMod 16) = _; push_cast; ring
  rw [hre, him]
  have h16 : (16 : ZMod 16) = 0 := rfl
  linear_combination 4 * hE + 8 * hT' + (((p - 1) / 8 : ℕ) - Ti - Tm) * h16
end QuarterSumLadder
