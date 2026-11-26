-- Prove2me | solution 1 for SemigroupBetti.GenData.three_le_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:33:09.494174+00:00
-- url     : https://prove2.me/submissions/b2898aa8-4df6-4820-bffe-f61aa8c3b0fe

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_B_lt_W
public import Theorems.Thm_SemigroupBetti_GenData_two_le_B

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : 3 ≤ G.W := by have := G.two_le_B; have := G.B_lt_W; omega
end SemigroupBetti.GenData
