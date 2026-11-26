-- Prove2me | solution 1 for SemigroupBetti.GenData.exc_R
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:13:23.380217+00:00
-- url     : https://prove2.me/submissions/6302b663-d709-4e68-944d-56f301f6f0ec

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
theorem _root_.solution : G.R = G.W - 1 := by
  have := G.three_le_W; unfold R; omega
end SemigroupBetti.GenData
