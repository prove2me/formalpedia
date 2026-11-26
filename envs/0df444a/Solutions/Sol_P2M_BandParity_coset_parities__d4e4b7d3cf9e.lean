-- Prove2me | solution 1 for P2M_BandParity_coset_parities__d4e4b7d3cf9e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:08.272189+00:00
-- url     : https://prove2.me/submissions/4ed2565e-a5dc-4609-a1fb-820d8d9c462d

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_char_neg
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_gi_sq
public import Theorems.Thm_BandParity_half_sum
public import Theorems.Thm_BandParity_im_add_gi_mul
public import Theorems.Thm_BandParity_parSign_neg
public import Theorems.Thm_BandParity_parSign_two_mul_of_lt
public import Theorems.Thm_BandParity_quartic_apply_neg_one
public import Theorems.Thm_BandParity_re_add_gi_mul
public import Theorems.Thm_BandParity_sum_char_mul_odd
public import Theorems.Thm_BandParity_sum_eq_two_nsmul_half
public import Theorems.Thm_P2M_BandParity_T_eq__1be22a5fd3a8
public import Theorems.Thm_P2M_BandParity_two_ne_zero__f8063a3397df
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    ∑ u ∈ cls χ 1, parSign u = k χ + 2 * t χ ∧ ∑ u ∈ cls χ gi, parSign u = t χ - 2 * k χ := by
  have hp2 : p ≠ 2 := by omega
  have hodd := quartic_apply_neg_one χ hχ hp8
  have h2 := two_ne_zero' (p := p) hp2
  have ha := sum_char_mul_odd hχ hodd parSign (fun x hx => parSign_neg hp2 hx)
  have hb : ∑ x : ZMod p, χ 2 * (χ x * (parSign (2 * x) : GaussianInt)) =
      ∑ x : ZMod p, χ x * (parSign x : GaussianInt) :=
    Fintype.sum_equiv (Equiv.mulLeft₀ (2 : ZMod p) h2) _ _ fun x => by
      simp only [Equiv.mulLeft₀_apply, map_mul]; ring
  have hc := sum_eq_two_nsmul_half hp2 (fun x => χ x * (parSign (2 * x) : GaussianInt))
    (by simp [MulChar.map_zero]) (fun x => by
      by_cases hx : x = 0
      · subst hx; simp
      · simp only [char_neg hodd, mul_neg, parSign_neg hp2 (mul_ne_zero h2 hx)]; push_cast
        ring)
  have hc' : ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p),
      χ x * (parSign (2 * x) : GaussianInt) =
      ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), χ x := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [mem_filter, mem_univ, true_and] at hx
    rw [parSign_two_mul_of_lt hp2 hx]; simp
  have hd := half_sum hp2 χ hodd
  rw [T_eq' hχ hp5, hpin] at hd
  have hp0 : (p : GaussianInt) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  set half := ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), χ x with hhalf
  have hd' : gi * half = (1 - 2 * gi) * ((k χ : GaussianInt) + gi * t χ) := by
    apply mul_left_cancel₀ hp0; linear_combination hd
  rw [← Finset.mul_sum, hc, hc', two_nsmul, hpin] at hb
  rw [ha] at hb
  set A := ∑ u ∈ cls χ 1, parSign u with hA
  set B := ∑ u ∈ cls χ gi, parSign u with hB
  have key : (A : GaussianInt) + gi * B =
      ((k χ + 2 * t χ : ℤ) : GaussianInt) + gi * ((t χ - 2 * k χ : ℤ) : GaussianInt) := by
    have h2' : (2 : GaussianInt) ≠ 0 := two_ne_zero
    apply mul_left_cancel₀ h2'
    have e1 : ((k χ + 2 * t χ : ℤ) : GaussianInt) = (k χ : GaussianInt) + 2 * t χ := by push_cast; ring
    have e2 : ((t χ - 2 * k χ : ℤ) : GaussianInt) = (t χ : GaussianInt) - 2 * k χ := by push_cast; ring
    rw [e1, e2]
    linear_combination -hb + 2 * hd' + (-4 * (t χ : GaussianInt)) * gi_sq
  have kr := congrArg Zsqrtd.re key
  have ki := congrArg Zsqrtd.im key
  rw [re_add_gi_mul, re_add_gi_mul] at kr
  rw [im_add_gi_mul, im_add_gi_mul] at ki
  exact ⟨kr, ki⟩
end BandParity
