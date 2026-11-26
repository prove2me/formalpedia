-- Prove2me | solution 1 for QuadraticFloor.osum_negOnePow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:52.092857+00:00
-- url     : https://prove2.me/submissions/1eb3db4b-572d-4c1b-89b4-4e1f50aeca30

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
public import Theorems.Thm_QuadraticFloor_osum_zero
public import Theorems.Thm_QuadraticFloor_osum_succ
public import Theorems.Thm_QuadraticFloor_eq_of_osum_step

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (t : ℤ) : 2 * osum t (fun j => (j.negOnePow : ℤ)) = 1 - (t.negOnePow : ℤ) := by
  have := eq_of_osum_step (F := fun c => 1 - (c.negOnePow : ℤ) - 2 * osum c (fun j => (j.negOnePow : ℤ)))
    (g := fun _ => 0) (by
      intro c
      simp only [osum_succ, Int.negOnePow_succ, Units.val_neg]
      ring) t
  simp only [osum_zero, Int.negOnePow_zero, Units.val_one] at this
  have h0 : osum t (fun _ : ℤ => (0 : ℤ)) = 0 := by unfold osum; split_ifs <;> simp
  rw [h0] at this
  linarith
end QuadraticFloor
