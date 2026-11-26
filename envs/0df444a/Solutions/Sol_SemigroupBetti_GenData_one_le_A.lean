-- Prove2me | solution 1 for SemigroupBetti.GenData.one_le_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:34.863814+00:00
-- url     : https://prove2.me/submissions/92749817-38d7-4c26-8739-26eaf6ce5e49

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_A_pos

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : 1 ≤ G.A := G.A_pos
end SemigroupBetti.GenData
