-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.nine_typeCount_mul_badNonheavy_card_le_five_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:12:26.44468+00:00
-- url     : https://prove2.me/submissions/9e377716-6f45-44d4-b652-2804ca40df86

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_nine_typeCount_le_five_heavyIncidences_of_badNonheavy

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    9 * typeCount *
        (badNonheavyLayerSet Delta twistSample w).card ≤
      5 *
        neighborEdgeCount twistSample
          (badNonheavyLayerSet Delta twistSample w)
          (heavyLayerSet Delta w) := by
  calc
    9 * typeCount *
        (badNonheavyLayerSet Delta twistSample w).card =
        ∑ _u ∈ badNonheavyLayerSet Delta twistSample w,
          9 * typeCount := by
      rw [Finset.sum_const_nat (fun _ _ => rfl)]
      ring
    _ ≤ ∑ u ∈ badNonheavyLayerSet Delta twistSample w,
        5 *
          neighborIncidenceCount twistSample
            (heavyLayerSet Delta w) u := by
      apply Finset.sum_le_sum
      intro u hu
      exact
        nine_typeCount_le_five_heavyIncidences_of_badNonheavy
          Delta twistSample w u hu
    _ = 5 *
        neighborEdgeCount twistSample
          (badNonheavyLayerSet Delta twistSample w)
          (heavyLayerSet Delta w) := by
      rw [neighborEdgeCount, Finset.mul_sum]
end QEC.Coding.FiberBundle.TwistGraph
