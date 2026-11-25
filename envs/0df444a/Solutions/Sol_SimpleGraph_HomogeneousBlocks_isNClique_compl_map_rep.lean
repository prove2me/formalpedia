-- Prove2me | solution 1 for SimpleGraph.HomogeneousBlocks.isNClique_compl_map_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:21.381455+00:00
-- url     : https://prove2.me/submissions/6f636e47-3686-4735-bf21-0413c74b04f7

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Definitions.Def_RamseyReservoir_HomogeneousBlocks
public import Theorems.Thm_SimpleGraph_HomogeneousBlocks_compl_adj_of_quotient_compl_adj

set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open SimpleGraph
variable {V ι : Type*}
open SimpleGraph.HomogeneousBlocks
variable {G : SimpleGraph V} (F : G.HomogeneousBlocks ι)
namespace SimpleGraph.HomogeneousBlocks
theorem _root_.solution {m : ℕ} {I : Finset ι} (hI : F.quotientᶜ.IsNClique m I) :
    Gᶜ.IsNClique m (I.map F.repEmbedding) := by
  refine ⟨?_, by rw [card_map, hI.card_eq]⟩
  rintro _ hx _ hy hxy
  obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
  obtain ⟨j, hj, rfl⟩ := mem_map.mp hy
  exact F.compl_adj_of_quotient_compl_adj (hI.isClique hi hj fun h => hxy (by rw [h]))
    (F.rep_mem i) (F.rep_mem j)
end SimpleGraph.HomogeneousBlocks
