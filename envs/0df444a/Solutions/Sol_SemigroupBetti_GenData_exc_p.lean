-- Prove2me | solution 1 for SemigroupBetti.GenData.exc_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:13:25.091803+00:00
-- url     : https://prove2.me/submissions/143c9390-0ccf-43e1-8f9d-2c2cb6645e15

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
public import Theorems.Thm_SemigroupBetti_GenData_three_le_W


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
variable {G}
variable (hA : G.A = 1) (hB : G.B = G.W - 1)
include hA hB
set_option linter.unusedSectionVars false
namespace SemigroupBetti.GenData
theorem _root_.solution : G.p = 1 := by
  have := G.three_le_W
  have ht : G.t = 1 := by unfold t; omega
  have hs : G.s = 1 := hA
  unfold p dg; rw [ht, hs]; rfl
end SemigroupBetti.GenData
