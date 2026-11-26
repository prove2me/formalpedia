-- Prove2me | solution 1 for SemigroupBetti.GenData.eq_critVertex_of_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:09:35.197826+00:00
-- url     : https://prove2.me/submissions/ba2f57a0-4594-4791-a3d6-a1b1d48a8e5f

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
public import Theorems.Thm_SemigroupBetti_GenData_critVertex_not_adj

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (i : Fin 4) {z : G.fiber (G.crit i * G.n i)}
    (h : (G.nabla _).Reachable (G.critVertex i) z) : z = G.critVertex i := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (G.critVertex_not_adj i _)
end SemigroupBetti.GenData
