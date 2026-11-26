-- Prove2me | solution 1 for SemigroupBetti.GenData.W_eq_B_add_t
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:11:01.553785+00:00
-- url     : https://prove2.me/submissions/8238d6c8-a894-42e3-a1a6-e5c978d7e044

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
theorem _root_.solution : G.W = G.B + G.t := by have := G.B_lt_W; unfold t; omega
end SemigroupBetti.GenData
