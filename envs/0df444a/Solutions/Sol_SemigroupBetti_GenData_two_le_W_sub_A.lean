-- Prove2me | solution 1 for SemigroupBetti.GenData.two_le_W_sub_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:33:21.368502+00:00
-- url     : https://prove2.me/submissions/92a9537c-2374-4ca8-9cc1-b96d717ccc2a

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_A_lt_B
public import Theorems.Thm_SemigroupBetti_GenData_B_lt_W

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : 2 ≤ G.W - G.A := by
  have := G.A_lt_B; have := G.B_lt_W; omega
end SemigroupBetti.GenData
