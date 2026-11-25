-- Prove2me | solution 1 for SmallRatio.smallRatioSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:23:15.164282+00:00
-- url     : https://prove2.me/submissions/17f2efd1-3f62-433e-8b44-7a5a33ffaaea

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
theorem _root_.solution (hp : p.Prime) : smallRatioSum p 0 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  unfold smallRatioSum
  apply sum_eq_zero
  intro u hu
  apply sum_eq_zero
  intro v hv
  rw [mem_Icc] at hu hv
  by_cases hcond : Nat.Coprime u v ∧ 2 * u * v < p
  · rw [if_pos hcond]
    have hu' : (u : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      have : u ≤ 2 * u * v := by nlinarith [hv.1]
      omega
    have h1 : ¬ (((0 * v : ℕ) : ZMod p) = (u : ZMod p)) := by
      rw [zero_mul, Nat.cast_zero]; exact fun h => hu' h.symm
    have h2 : ¬ (((0 * v : ℕ) : ZMod p) = -(u : ZMod p)) := by
      rw [zero_mul, Nat.cast_zero]; exact fun h => hu' (neg_eq_zero.1 h.symm)
    rw [if_neg h1, if_neg h2]; simp
  · rw [if_neg hcond]
end SmallRatio
