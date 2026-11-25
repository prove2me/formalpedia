-- Prove2me | solution 1 for SimpleGraph.HomogeneousBlocks.compl_adj_of_quotient_compl_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:32:42.675349+00:00
-- url     : https://prove2.me/submissions/cb7d64ba-4a97-43f4-93fc-0e058d384d74

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Definitions.Def_RamseyReservoir_HomogeneousBlocks
public import Theorems.Thm_SimpleGraph_HomogeneousBlocks_quotient_adj

set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open SimpleGraph
variable {V ι : Type*}
open SimpleGraph.HomogeneousBlocks
variable {G : SimpleGraph V} (F : G.HomogeneousBlocks ι)
namespace SimpleGraph.HomogeneousBlocks
theorem _root_.solution {i j : ι} (h : F.quotientᶜ.Adj i j) {x y : V}
    (hx : x ∈ F.block i) (hy : y ∈ F.block j) : Gᶜ.Adj x y := by
  rw [compl_adj] at h ⊢
  refine ⟨F.ne_of_mem_block h.1 hx hy, ?_⟩
  rcases F.homogeneous i j h.1 with hall | hnone
  · exact absurd (F.quotient_adj.mpr ⟨h.1, hall⟩) h.2
  · exact hnone x hx y hy
end SimpleGraph.HomogeneousBlocks
