-- Prove2me | solution 1 for SemigroupBetti.GenData.mem_singletonDegrees_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:17:48.43061+00:00
-- url     : https://prove2.me/submissions/701ef00a-dcf6-40f1-83a8-e58bfb36032b

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
public import Theorems.Thm_SemigroupBetti_GenData_mem_singletonDegrees
public import Theorems.Thm_SemigroupBetti_GenData_le_H_of_contributes


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} (hd : G.contributes d) (hS : G.HasSingletonComp d) :
    d ∈ G.singletonDegrees :=
  G.mem_singletonDegrees.2 ⟨G.le_H_of_contributes hd, hd, hS⟩
end SemigroupBetti.GenData
