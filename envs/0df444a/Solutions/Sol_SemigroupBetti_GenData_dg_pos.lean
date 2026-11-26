-- Prove2me | solution 1 for SemigroupBetti.GenData.dg_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:57:47.559469+00:00
-- url     : https://prove2.me/submissions/45d1ce06-4a89-4ce8-bb4c-87bea0058881

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
public import Theorems.Thm_SemigroupBetti_GenData_s_pos

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : 1 ≤ G.dg := Nat.gcd_pos_of_pos_left _ G.s_pos
end SemigroupBetti.GenData
