-- Prove2me | solution 1 for SemigroupBetti.GenData.one_le_g
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:30.195488+00:00
-- url     : https://prove2.me/submissions/acb4a94a-6a6a-43ef-8b4d-3f1596be7bcc

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_g_pos

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : 1 ≤ G.g := G.g_pos
end SemigroupBetti.GenData
