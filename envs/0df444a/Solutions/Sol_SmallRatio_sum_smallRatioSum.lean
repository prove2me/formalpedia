-- Prove2me | solution 1 for SmallRatio.sum_smallRatioSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:22:21.785115+00:00
-- url     : https://prove2.me/submissions/3eb58853-f2ac-4d03-bc8c-2ad4fa457dc2

module
public import Definitions.Def_SmallRatio_Main
public import Definitions.Def_SmallRatio_Subgroup
public import Theorems.Thm_SmallRatio_den_one
public import Theorems.Thm_SmallRatio_den_zero
public import Theorems.Thm_SmallRatio_rem_one
public import Theorems.Thm_SmallRatio_rem_zero
attribute [local simp] SmallRatio.den_one
attribute [local simp] SmallRatio.den_zero
attribute [local simp] SmallRatio.rem_one
attribute [local simp] SmallRatio.rem_zero



set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {p : ℕ}
namespace SmallRatio
theorem _root_.solution (hp : p.Prime) (H : Finset (ZMod p)) :
    ∑ x ∈ H, smallRatioSum p x.val = subgroupSmallRatio p H := by
  have : Fact p.Prime := ⟨hp⟩
  unfold smallRatioSum subgroupSmallRatio
  rw [sum_comm]
  refine sum_congr rfl fun u hu => ?_
  rw [sum_comm]
  refine sum_congr rfl fun v hv => ?_
  by_cases hcond : Nat.Coprime u v ∧ 2 * u * v < p
  · simp only [if_pos hcond]
    rw [mem_Icc] at hv hu
    have hv0 : (v : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      have : v ≤ 2 * u * v := by nlinarith [hu.1]
      omega
    have key1 : ∀ x : ZMod p, ((x.val * v : ℕ) : ZMod p) = (u : ZMod p) ↔
        x = (u : ZMod p) * (v : ZMod p)⁻¹ := by
      intro x
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, eq_mul_inv_iff_mul_eq₀ hv0]
    have key2 : ∀ x : ZMod p, ((x.val * v : ℕ) : ZMod p) = -(u : ZMod p) ↔
        x = -((u : ZMod p) * (v : ZMod p)⁻¹) := by
      intro x
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, neg_mul_eq_neg_mul, eq_mul_inv_iff_mul_eq₀ hv0]
    rw [← sum_div, sum_sub_distrib]
    congr 2
    · simp_rw [key1]; rw [sum_ite_eq']
    · simp_rw [key2]; rw [sum_ite_eq']
  · simp only [if_neg hcond, sum_const_zero]
end SmallRatio
