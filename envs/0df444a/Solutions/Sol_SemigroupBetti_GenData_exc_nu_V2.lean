-- Prove2me | solution 1 for SemigroupBetti.GenData.exc_nu_V2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:06:44.875215+00:00
-- url     : https://prove2.me/submissions/a553b889-1411-4549-ba68-3c383a063511

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
public import Theorems.Thm_SemigroupBetti_GenData_exc_U2
public import Theorems.Thm_SemigroupBetti_GenData_exc_V2
public import Theorems.Thm_SemigroupBetti_GenData_identity2
public import Theorems.Thm_SemigroupBetti_GenData_nu_single


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
theorem _root_.solution : G.nu ![0, 1, 0, G.W - 2] = (G.W - 1) * G.n 2 := by
  rw [← exc_V2 hA hB, ← G.identity2.1, exc_U2 hA hB, G.nu_single]
end SemigroupBetti.GenData
