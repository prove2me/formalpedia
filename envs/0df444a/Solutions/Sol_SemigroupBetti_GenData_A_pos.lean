-- Prove2me | solution 1 for SemigroupBetti.GenData.A_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:44.269531+00:00
-- url     : https://prove2.me/submissions/c84e6f8f-68ad-465b-972c-76dd2eaf62fe

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_a_eq

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : 0 < G.A := by
  have h := G.a_pos; rw [G.a_eq] at h; exact Nat.pos_of_mul_pos_left h
end SemigroupBetti.GenData
