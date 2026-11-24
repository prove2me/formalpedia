-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.dist_on_geodesic_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:32:21.725435+00:00
-- url     : https://prove2.me/submissions/1fd9cb46-94bf-4035-9b92-ce78be66da3f

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_dist_eq_of_mem_geodesic

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected)
    {u n v z : α} (hun : G.Adj u n) (p : G.Walk n v)
    (hp : (p.cons hun).length = G.dist u v) (hz : z ∈ p.support) :
    G.dist u z = G.dist n z + 1 := by
  have htail := length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons p hun)
  have hsum := dist_add_dist_eq_of_mem_geodesic p htail hz
  have hlen : G.dist u v = G.dist n v + 1 := by
    simpa only [Walk.length_cons, htail] using hp.symm
  have htri := hG.dist_triangle (u := u) (v := z) (w := v)
  have htri' := hG.dist_triangle (u := u) (v := n) (w := z)
  have hdistun : G.dist u n = 1 := dist_eq_one_iff_adj.mpr hun
  omega
end WrittenOnTheWallII.GraphConjecture84
