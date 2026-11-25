-- Prove2me | solution 1 for SimpleGraph.HomogeneousBlocks.quotient_adj_iff_adj_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:00.7058+00:00
-- url     : https://prove2.me/submissions/0c6c2831-00c3-40e2-ba5d-594304e90694

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Definitions.Def_RamseyReservoir_HomogeneousBlocks
public import Theorems.Thm_SimpleGraph_HomogeneousBlocks_quotient_adj
public import Theorems.Thm_SimpleGraph_HomogeneousBlocks_adj_of_quotient_adj

set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open SimpleGraph
variable {V ι : Type*}
open SimpleGraph.HomogeneousBlocks
variable {G : SimpleGraph V} (F : G.HomogeneousBlocks ι)
namespace SimpleGraph.HomogeneousBlocks
theorem _root_.solution {i j : ι} : F.quotient.Adj i j ↔ G.Adj (F.rep i) (F.rep j) := by
  refine ⟨fun h => F.adj_of_quotient_adj h (F.rep_mem i) (F.rep_mem j), fun h => ?_⟩
  have hij : i ≠ j := fun hij => by subst hij; exact G.irrefl h
  rcases F.homogeneous i j hij with hall | hnone
  · exact F.quotient_adj.mpr ⟨hij, hall⟩
  · exact absurd h (hnone _ (F.rep_mem i) _ (F.rep_mem j))
end SimpleGraph.HomogeneousBlocks
