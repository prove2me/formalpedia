-- Prove2me | solution 1 for SemigroupBetti.GenData.A_lt_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:05.962258+00:00
-- url     : https://prove2.me/submissions/644ede12-80e3-4f5d-9bac-66c9296ca75a

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_a_eq
public import Theorems.Thm_SemigroupBetti_GenData_b_eq

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.A < G.B := by
  have h := G.a_lt_b; rw [G.a_eq, G.b_eq] at h; exact Nat.lt_of_mul_lt_mul_left h
end SemigroupBetti.GenData
