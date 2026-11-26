-- Prove2me | solution 1 for SemigroupBetti.GenData.two_le_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:11.946927+00:00
-- url     : https://prove2.me/submissions/c199c876-fb85-47fb-9280-d09e5d103627

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_A_pos
public import Theorems.Thm_SemigroupBetti_GenData_A_lt_B

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : 2 ≤ G.B := by have := G.A_pos; have := G.A_lt_B; omega
end SemigroupBetti.GenData
