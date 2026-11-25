-- Prove2me | solution 1 for SimpleGraph.HomogeneousBlocks.isNClique_map_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:39.226985+00:00
-- url     : https://prove2.me/submissions/10b61ea6-7b50-4847-aa71-cdf92f86a02a

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Definitions.Def_RamseyReservoir_HomogeneousBlocks
public import Theorems.Thm_SimpleGraph_HomogeneousBlocks_quotient_adj_iff_adj_rep

set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open SimpleGraph
variable {V ι : Type*}
open SimpleGraph.HomogeneousBlocks
variable {G : SimpleGraph V} (F : G.HomogeneousBlocks ι)
namespace SimpleGraph.HomogeneousBlocks
theorem _root_.solution {m : ℕ} {I : Finset ι} (hI : F.quotient.IsNClique m I) :
    G.IsNClique m (I.map F.repEmbedding) := by
  refine ⟨?_, by rw [card_map, hI.card_eq]⟩
  rintro _ hx _ hy hxy
  obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
  obtain ⟨j, hj, rfl⟩ := mem_map.mp hy
  exact F.quotient_adj_iff_adj_rep.mp (hI.isClique hi hj fun h => hxy (by rw [h]))
end SimpleGraph.HomogeneousBlocks
