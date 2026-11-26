-- Prove2me | solution 1 for SemigroupBetti.GenData.p_add_q_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:10:50.881275+00:00
-- url     : https://prove2.me/submissions/65e1c519-809f-4a3a-9d21-a52819aaf2d7

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
public import Theorems.Thm_SemigroupBetti_GenData_dg_pos
public import Theorems.Thm_SemigroupBetti_GenData_dg_mul_p_add_q

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.p + G.q ≤ G.s + G.t := by
  rw [← G.dg_mul_p_add_q]; exact Nat.le_mul_of_pos_left _ G.dg_pos
end SemigroupBetti.GenData
