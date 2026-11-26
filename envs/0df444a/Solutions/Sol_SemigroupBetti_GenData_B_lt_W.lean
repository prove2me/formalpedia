-- Prove2me | solution 1 for SemigroupBetti.GenData.B_lt_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:09.951419+00:00
-- url     : https://prove2.me/submissions/066835c6-c29b-418c-bbb9-9e7c162aa439

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_b_eq
public import Theorems.Thm_SemigroupBetti_GenData_w_eq

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.B < G.W := by
  have h := G.b_lt_w; rw [G.b_eq, G.w_eq] at h; exact Nat.lt_of_mul_lt_mul_left h
end SemigroupBetti.GenData
