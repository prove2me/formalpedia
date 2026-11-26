-- Prove2me | solution 1 for SemigroupBetti.GenData.coord_le_of_contributes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:08:27.750047+00:00
-- url     : https://prove2.me/submissions/7cd94bba-c756-48e5-8f06-7d864920bfc8

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_exists_not_reachable
public import Theorems.Thm_SemigroupBetti_GenData_reachable_of_coord_gt
public import Theorems.Thm_SemigroupBetti_SharesVar_symm


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} (h : G.contributes d) (z : G.fiber d) (i : Fin 4) :
    z.1 i ≤ G.n 3 := by
  by_contra hc
  push Not at hc
  obtain ⟨y, y', hyy'⟩ := G.exists_not_reachable h
  exact hyy' (((G.reachable_of_coord_gt z y hc).symm).trans (G.reachable_of_coord_gt z y' hc))
end SemigroupBetti.GenData
