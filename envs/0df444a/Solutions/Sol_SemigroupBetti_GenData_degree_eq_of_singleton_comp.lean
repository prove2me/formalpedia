-- Prove2me | solution 1 for SemigroupBetti.GenData.degree_eq_of_singleton_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:10:22.773185+00:00
-- url     : https://prove2.me/submissions/6294fc82-5565-4d02-8040-cde86bbdc883

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
theorem _root_.solution {d : ℕ} (hd : G.contributes d) {i : Fin 4}
    {C : (G.nabla d).ConnectedComponent} (hC : G.compSupp C = {i}) :
    d = G.crit i * G.n i := by
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h z => exact (G.singleton_comp_vertex hd hC z rfl).2
end SemigroupBetti.GenData
