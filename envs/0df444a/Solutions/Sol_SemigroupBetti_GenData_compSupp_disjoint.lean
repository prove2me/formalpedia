-- Prove2me | solution 1 for SemigroupBetti.GenData.compSupp_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:53:57.104455+00:00
-- url     : https://prove2.me/submissions/012753a2-dde3-4f98-bbb9-237c29cacef3

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_mem_compSupp
public import Theorems.Thm_SemigroupBetti_GenData_reachable_of_sharesVar

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} {C C' : (G.nabla d).ConnectedComponent} (h : C ≠ C') :
    Disjoint (G.compSupp C) (G.compSupp C') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  obtain ⟨z, rfl, hz⟩ := G.mem_compSupp.1 hi
  obtain ⟨z', rfl, hz'⟩ := G.mem_compSupp.1 hi'
  exact h (SimpleGraph.ConnectedComponent.sound (G.reachable_of_sharesVar ⟨i, hz, hz'⟩))
end SemigroupBetti.GenData
