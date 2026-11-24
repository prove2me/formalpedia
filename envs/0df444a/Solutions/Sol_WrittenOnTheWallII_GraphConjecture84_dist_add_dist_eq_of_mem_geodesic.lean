-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.dist_add_dist_eq_of_mem_geodesic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:23:21.095638+00:00
-- url     : https://prove2.me/submissions/481325d9-6686-4dd9-bac9-239d09dac4c5

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} {u v z : α}
    (p : G.Walk u v) (hp : p.length = G.dist u v) (hz : z ∈ p.support) :
    G.dist u z + G.dist z v = G.dist u v := by
  have htake := length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hz)
  have hdrop := length_eq_dist_of_subwalk hp (p.isSubwalk_dropUntil hz)
  have hlen := congrArg Walk.length (p.take_spec hz)
  simpa only [Walk.length_append, htake, hdrop, hp] using hlen
end WrittenOnTheWallII.GraphConjecture84
