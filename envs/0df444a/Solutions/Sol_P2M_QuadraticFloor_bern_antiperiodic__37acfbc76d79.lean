-- Prove2me | solution 1 for P2M_QuadraticFloor_bern_antiperiodic__37acfbc76d79
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:54.834026+00:00
-- url     : https://prove2.me/submissions/3cbc993e-4c11-46eb-9e9a-9aa980dde7e9

module
public import Definitions.Def_QuadraticFloor_Eta
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Theorems.Thm_QuadraticFloor_sum_Icc_one

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (f : ℕ → ℂ) {h : ℕ} (hh : 0 < h) (hf : ∀ x, f (x + h) = -f x) :
    bern (2 * h) f = -(1 / 2) * ∑ x ∈ Icc 1 h, f x := by
  unfold bern
  rw [sum_Icc_one, sum_Icc_one, two_mul, sum_range_add]
  have hs : ∀ k ∈ range h, (((h + k + 1 : ℕ) : ℂ) * f (h + k + 1)) =
      -(((k + 1 : ℕ) : ℂ) * f (k + 1)) - (h : ℂ) * f (k + 1) := by
    intro k _
    rw [show h + k + 1 = (k + 1) + h by ring, hf]
    push_cast; ring
  rw [sum_congr rfl hs, sum_sub_distrib, sum_neg_distrib, ← mul_sum]
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  push_cast
  field_simp
  ring
end QuadraticFloor
