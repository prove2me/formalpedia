-- Prove2me | solution 1 for SemigroupBetti.GenData.dg_mul_p_add_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:02:28.8338+00:00
-- url     : https://prove2.me/submissions/6ae5aac3-ddbb-4c02-a6b0-1752b9498409

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
public import Theorems.Thm_SemigroupBetti_GenData_dg_mul_p
public import Theorems.Thm_SemigroupBetti_GenData_dg_mul_q

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.dg * (G.p + G.q) = G.s + G.t := by
  rw [mul_add, G.dg_mul_p, G.dg_mul_q, add_comm]
end SemigroupBetti.GenData
