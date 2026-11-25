-- Prove2me | solution 1 for SmallRatio.sum_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:16:07.648459+00:00
-- url     : https://prove2.me/submissions/676df116-87cb-4d30-931d-698c3e95ef9f

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity
public import Theorems.Thm_SmallRatio_sum_mul_mod_perm

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution (h k : ℕ) (hh : 0 < h) (hc : Nat.Coprime h k) :
    2 * ∑ j ∈ range h, ((k * j / h : ℕ) : ℤ) = ((h : ℤ) - 1) * ((k : ℤ) - 1) := by
  have hperm := sum_mul_mod_perm k h hh (Nat.Coprime.symm hc) (fun r => ((r : ℕ) : ℤ))
  have hmod : ∀ j ∈ range h, ((k * j % h : ℕ) : ℤ) = (k : ℤ) * j - h * ((k * j / h : ℕ) : ℤ) := by
    intro j _
    have := Nat.mod_add_div (k * j) h
    have : ((k * j % h : ℕ) : ℤ) + h * ((k * j / h : ℕ) : ℤ) = (k : ℤ) * j := by exact_mod_cast this
    linarith
  rw [sum_congr rfl hmod, sum_sub_distrib, ← mul_sum, ← mul_sum] at hperm
  have hs : 2 * ∑ j ∈ range h, (j : ℤ) = (h : ℤ) * (h - 1) := by
    have := Finset.sum_range_id_mul_two h
    have : ((∑ i ∈ range h, i : ℕ) : ℤ) * 2 = ((h * (h - 1) : ℕ) : ℤ) := by exact_mod_cast this
    push_cast [Nat.cast_sub (by omega : 1 ≤ h)] at this
    linarith
  have hh' : (h : ℤ) ≠ 0 := by exact_mod_cast hh.ne'
  apply mul_left_cancel₀ hh'
  nlinarith [hperm, hs]
end SmallRatio
