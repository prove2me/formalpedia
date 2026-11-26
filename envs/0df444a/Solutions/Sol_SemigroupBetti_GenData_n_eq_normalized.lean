-- Prove2me | solution 1 for SemigroupBetti.GenData.n_eq_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:33:46.721473+00:00
-- url     : https://prove2.me/submissions/0cb27a15-dae8-492f-8506-04ad77aa13b1

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_a_eq
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
theorem _root_.solution : G.n = ![G.m, G.m + G.g * G.A, G.m + G.g * G.B, G.m + G.g * G.W] := by
  rw [← G.a_eq, ← G.b_eq, ← G.w_eq]; rfl
end SemigroupBetti.GenData
