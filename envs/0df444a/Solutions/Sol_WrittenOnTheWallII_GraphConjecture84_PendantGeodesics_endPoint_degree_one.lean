-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.endPoint_degree_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:34:13.273555+00:00
-- url     : https://prove2.me/submissions/89d94782-0827-4c8e-9808-c74afa1c8138

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_adjacent_start_eq_snd_of_geodesic
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_length_pos_iff

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
open WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)
namespace WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
theorem _root_.solution [DecidableRel G.Adj] (hG : G.Connected) (c : ↥(K : Set α))
    (hpos : 0 < (F.path c).length) : G.degree (F.endPoint c) = 1 := by
  classical
  have hec := (F.length_pos_iff hG c).mp hpos
  let q := (F.path c).reverse
  have hq : q.length = G.dist (F.endPoint c) c := by
    simpa only [q, Walk.length_reverse, SimpleGraph.dist_comm] using F.geodesic c
  have hqn : ¬ q.Nil := q.not_nil_of_ne hec
  apply degree_eq_one_iff_existsUnique_adj.mpr
  refine ⟨q.snd, q.adj_snd hqn, ?_⟩
  intro w hew
  have hw := F.closed c _ (F.path c).end_mem_support hec w hew
  apply adjacent_start_eq_snd_of_geodesic hG q hq _ hew
  simpa only [q, Walk.support_reverse, List.mem_reverse] using hw
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
