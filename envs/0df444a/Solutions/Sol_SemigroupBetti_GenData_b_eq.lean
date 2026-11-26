-- Prove2me | solution 1 for SemigroupBetti.GenData.b_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:24.978143+00:00
-- url     : https://prove2.me/submissions/c04ccb8e-a407-4346-aee4-ce0e338b0600

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_SharesVar_symm
public import Theorems.Thm_SemigroupBetti_GenData_g_dvd_b

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.b = G.g * G.B := (Nat.mul_div_cancel' G.g_dvd_b).symm
end SemigroupBetti.GenData
