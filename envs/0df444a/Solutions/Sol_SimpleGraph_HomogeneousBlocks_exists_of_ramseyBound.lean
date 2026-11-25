-- Prove2me | solution 1 for SimpleGraph.HomogeneousBlocks.exists_of_ramseyBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:35:24.888556+00:00
-- url     : https://prove2.me/submissions/0edda7fa-75d2-4c63-a491-cd596e0461b6

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Definitions.Def_RamseyReservoir_HomogeneousBlocks
public import Theorems.Thm_SimpleGraph_HomogeneousBlocks_isNClique_map_rep
public import Theorems.Thm_SimpleGraph_HomogeneousBlocks_isNClique_compl_map_rep
public import Theorems.Thm_SimpleGraph_RamseyBound_exists_isNClique_subset


set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open SimpleGraph
variable {V ι : Type*}
open SimpleGraph.HomogeneousBlocks
variable {G : SimpleGraph V} (F : G.HomogeneousBlocks ι)
include F
namespace SimpleGraph.HomogeneousBlocks
theorem _root_.solution {n r s : ℕ} (h : RamseyBound n r s) {J : Finset ι} (hJ : n ≤ #J) :
    (∃ t, G.IsNClique r t) ∨ ∃ t, Gᶜ.IsNClique s t := by
  rcases h.exists_isNClique_subset F.quotient hJ with ⟨I, -, hI⟩ | ⟨I, -, hI⟩
  exacts [.inl ⟨_, F.isNClique_map_rep hI⟩, .inr ⟨_, F.isNClique_compl_map_rep hI⟩]
end SimpleGraph.HomogeneousBlocks
