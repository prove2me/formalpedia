-- Prove2me | solution 1 for SemigroupBetti.GenData.w_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:09.399476+00:00
-- url     : https://prove2.me/submissions/98373625-2c6c-420b-88e8-d7e511423355

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_SharesVar_symm
public import Theorems.Thm_SemigroupBetti_GenData_g_dvd_w

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.w = G.g * G.W := (Nat.mul_div_cancel' G.g_dvd_w).symm
end SemigroupBetti.GenData
