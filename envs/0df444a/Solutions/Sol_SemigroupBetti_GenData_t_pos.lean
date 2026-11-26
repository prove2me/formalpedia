-- Prove2me | solution 1 for SemigroupBetti.GenData.t_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:02:08.854582+00:00
-- url     : https://prove2.me/submissions/40e44f20-2b3f-46d9-90b0-44668b2ce6a3

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
public import Theorems.Thm_SemigroupBetti_GenData_B_lt_W


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : 1 ≤ G.t := by have := G.B_lt_W; unfold t; omega
end SemigroupBetti.GenData
