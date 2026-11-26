-- Prove2me | solution 1 for SemigroupBetti.GenData.s_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:56:37.438563+00:00
-- url     : https://prove2.me/submissions/31c646a4-0c9a-4549-a007-513af5c32b76

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
public import Theorems.Thm_SemigroupBetti_GenData_A_pos


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : 1 ≤ G.s := G.A_pos
end SemigroupBetti.GenData
