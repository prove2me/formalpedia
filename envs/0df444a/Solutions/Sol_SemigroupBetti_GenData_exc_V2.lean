-- Prove2me | solution 1 for SemigroupBetti.GenData.exc_V2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:04:53.821069+00:00
-- url     : https://prove2.me/submissions/6fcde4bc-37f9-4987-a2ae-33e240ef86d4

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_three_le_W
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.GenData.mem_fiber
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.nu_zero
attribute [local simp] SemigroupBetti.mem_supp



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
theorem _root_.solution : G.V2 = ![0, 1, 0, G.W - 2] := by
  have := G.three_le_W
  have h1 : G.W - G.B = 1 := by omega
  have h2 : G.B - G.A = G.W - 2 := by omega
  simp only [V2, h1, h2]
end SemigroupBetti.GenData
