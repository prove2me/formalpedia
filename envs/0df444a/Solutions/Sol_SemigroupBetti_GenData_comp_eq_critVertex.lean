-- Prove2me | solution 1 for SemigroupBetti.GenData.comp_eq_critVertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:16:24.72489+00:00
-- url     : https://prove2.me/submissions/1962d549-60b1-4f65-8e69-244b733e6aa7

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
public import Theorems.Thm_SemigroupBetti_GenData_singleton_comp_vertex

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {i : Fin 4} (hd : G.contributes (G.crit i * G.n i))
    {C : (G.nabla _).ConnectedComponent} (hC : G.compSupp C = {i}) :
    C = (G.nabla _).connectedComponentMk (G.critVertex i) := by
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h z =>
    have := (G.singleton_comp_vertex hd hC z rfl).1
    rw [show z = G.critVertex i from Subtype.ext this]
end SemigroupBetti.GenData
