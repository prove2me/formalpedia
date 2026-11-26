-- Prove2me | solution 1 for P2M_BandParity_lag_identity__1cd92334e44b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:13:27.257687+00:00
-- url     : https://prove2.me/submissions/f6776c1b-6fc7-447f-b7bb-a2cc1cb746b7

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_quadraticChar_neg
public import Theorems.Thm_BandParity_quadraticChar_eq_legendreSym
public import Theorems.Thm_BandParity_sum_alt_legendre
public import Theorems.Thm_BandParity_quadraticChar_of_char_one
public import Theorems.Thm_BandParity_quadraticChar_of_char_gi
public import Theorems.Thm_BandParity_distinct
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_ne_zero
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_parSign_neg
public import Theorems.Thm_BandParity_parSign_two_mul_of_lt
public import Theorems.Thm_BandParity_quartic_apply_neg_one
public import Theorems.Thm_BandParity_quartic_values
public import Theorems.Thm_BandParity_sum_alt_half
public import Theorems.Thm_BandParity_sum_cls_neg_even
public import Theorems.Thm_BandParity_sum_eq_two_nsmul_half
public import Theorems.Thm_BandParity_sum_filter_val
public import Theorems.Thm_BandParity_zero_ne_gi
public import Theorems.Thm_P2M_BandParity_sum_half_eq_sum_half__95af2de0d67d
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
theorem _root_.solution (hp8 : p % 8 = 5) :
    ∑ u ∈ cls χ gi, parSign u * parSign (2 * u) = kappa p := by
  have hp2 : p ≠ 2 := by omega
  have hp4 : p % 4 = 1 := by omega
  have hodd := quartic_apply_neg_one χ hχ hp8
  have h2 := two_ne_zero' (p := p) hp2
  set F : ZMod p → ℤ := fun x => parSign x * parSign (2 * x) with hF
  have hFeven : ∀ x ≠ 0, F (-x) = F x := by
    intro x hx
    have h2x : 2 * x ≠ 0 := mul_ne_zero h2 hx
    show parSign (-x) * parSign (2 * -x) = parSign x * parSign (2 * x)
    rw [show (2 : ZMod p) * -x = -(2 * x) by ring, parSign_neg hp2 hx, parSign_neg hp2 h2x]
    ring
  have hneg := sum_cls_neg_even hodd F hFeven gi_ne_zero
  -- pointwise: the nonresidue indicator is `(1 - (x/p))/2`
  have hpt : ∀ x : ZMod p,
      2 * ((if χ x = gi then F x else 0) + (if χ x = -gi then F x else 0)) =
        (if x = 0 then 0 else F x) - F x * quadraticChar (ZMod p) x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [MulChar.map_zero, zero_ne_gi, gi_ne_zero]
    · rcases quartic_values χ hχ hx with h | h | h | h
      · rw [quadraticChar_of_char_one hχ hx (Or.inl h)]; simp [hx, h, distinct]
      · rw [quadraticChar_of_char_gi hχ hx (Or.inl h)]; simp [hx, h, distinct]; ring
      · rw [quadraticChar_of_char_one hχ hx (Or.inr h)]; simp [hx, h, distinct]
      · rw [quadraticChar_of_char_gi hχ hx (Or.inr h)]; simp [hx, h, distinct]; ring
  have hsum : 2 * (∑ x ∈ cls χ gi, F x + ∑ x ∈ cls χ (-gi), F x) =
      ∑ x : ZMod p, (if x = 0 then 0 else F x) - ∑ x : ZMod p, F x * quadraticChar (ZMod p) x := by
    simp only [cls, Finset.sum_filter, ← Finset.sum_add_distrib, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => hpt x
  -- the unweighted sum vanishes
  have hA : ∑ x : ZMod p, (if x = 0 then 0 else F x) = 0 := by
    have h := sum_eq_two_nsmul_half hp2 (fun x => if x = 0 then 0 else F x) (by simp)
      (fun x => by
        by_cases hx : x = 0
        · subst hx; simp
        · simp [hx, hFeven x hx])
    rw [h, sum_half_eq_sum_half' _ (by simp)]
    have : ∑ x ∈ univ.filter (fun x : ZMod p => 0 < x.val ∧ 2 * x.val < p),
        (if x = 0 then 0 else F x) =
        ∑ x ∈ univ.filter (fun x : ZMod p => 0 < x.val ∧ 2 * x.val < p), (-1 : ℤ) ^ x.val := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [mem_filter, mem_univ, true_and] at hx
      have hx0 : x ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hx; omega
      simp only [hx0, ↓reduceIte]
      show parSign x * parSign (2 * x) = (-1) ^ x.val
      rw [parSign_two_mul_of_lt hp2 hx.2, mul_one]; rfl
    rw [this, sum_filter_val (fun v => 0 < v ∧ 2 * v < p) (fun v => (-1 : ℤ) ^ v),
      sum_alt_half hp4, smul_zero]
  -- the Legendre-weighted sum is `-4κ`
  have hB : ∑ x : ZMod p, F x * quadraticChar (ZMod p) x = -4 * kappa p := by
    have h := sum_eq_two_nsmul_half hp2 (fun x => F x * quadraticChar (ZMod p) x)
      (by simp)
      (fun x => by
        by_cases hx : x = 0
        · subst hx; simp
        · simp only [hFeven x hx, quadraticChar_neg hp4])
    rw [h, sum_half_eq_sum_half' _ (by simp)]
    have : ∑ x ∈ univ.filter (fun x : ZMod p => 0 < x.val ∧ 2 * x.val < p),
        F x * quadraticChar (ZMod p) x =
        ∑ x ∈ univ.filter (fun x : ZMod p => 0 < x.val ∧ 2 * x.val < p),
          (-1 : ℤ) ^ x.val * legendreSym p (x.val : ℤ) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [mem_filter, mem_univ, true_and] at hx
      show parSign x * parSign (2 * x) * quadraticChar (ZMod p) x = _
      rw [parSign_two_mul_of_lt hp2 hx.2, mul_one, quadraticChar_eq_legendreSym]; rfl
    rw [this, sum_filter_val (fun v => 0 < v ∧ 2 * v < p)
      (fun v => (-1 : ℤ) ^ v * legendreSym p (v : ℤ)), sum_alt_legendre hp8, two_nsmul]
    ring
  rw [hA, hB, hneg] at hsum
  linarith
end BandParity
