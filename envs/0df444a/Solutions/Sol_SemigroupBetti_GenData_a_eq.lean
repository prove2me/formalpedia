-- Prove2me | solution 1 for SemigroupBetti.GenData.a_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:44.059389+00:00
-- url     : https://prove2.me/submissions/52c64f3e-18c2-4b8a-81f2-461949cdd30b

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_SharesVar_symm
public import Theorems.Thm_SemigroupBetti_GenData_g_dvd_a

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.a = G.g * G.A := (Nat.mul_div_cancel' G.g_dvd_a).symm
end SemigroupBetti.GenData
