-- Prove2me | solution 1 for SemigroupBetti.GenData.two_le_R
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:02:36.073788+00:00
-- url     : https://prove2.me/submissions/e4ba174b-e1de-4913-88f0-1441a0219742

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
public import Theorems.Thm_SemigroupBetti_GenData_two_le_B
public import Theorems.Thm_SemigroupBetti_GenData_two_le_W_sub_A


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : 2 ≤ G.R := by
  have := G.two_le_B; have := G.two_le_W_sub_A; unfold R; omega
end SemigroupBetti.GenData
