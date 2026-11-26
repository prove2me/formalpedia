-- Prove2me | solution 1 for QuadraticFloor.sum_Ico_eq_add_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:28.641932+00:00
-- url     : https://prove2.me/submissions/d2798ef8-6d7a-4d1b-ade0-77aeeea89686

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (g : ℤ → ℤ) {a b : ℤ} (h : a < b) :
    ∑ j ∈ Ico a b, g j = g a + ∑ j ∈ Ico (a + 1) b, g j := by
  have : Ico a b = insert a (Ico (a + 1) b) := by
    ext j; simp only [mem_Ico, mem_insert]; omega
  rw [this, sum_insert (by simp)]
end QuadraticFloor
