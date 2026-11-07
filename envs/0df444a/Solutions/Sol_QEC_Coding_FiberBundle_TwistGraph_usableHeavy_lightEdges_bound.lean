-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.usableHeavy_lightEdges_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:12:35.515612+00:00
-- url     : https://prove2.me/submissions/39894692-af05-4cad-9d35-5cf60599344b

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_neighborIncidenceCount_le_two_mul_typeCount

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
    100 *
        neighborEdgeCount twistSample
          (usableHeavyLayerSet Delta twistSample w)
          (lightLayerSet Delta w) ≤
      200 * typeCount *
        (usableHeavyLayerSet Delta twistSample w).card := by
  let good := usableHeavyLayerSet Delta twistSample w
  calc
    100 *
        neighborEdgeCount twistSample good (lightLayerSet Delta w) =
        ∑ u ∈ good,
          100 *
            neighborIncidenceCount twistSample
              (lightLayerSet Delta w) u := by
      rw [neighborEdgeCount, Finset.mul_sum]
    _ ≤ ∑ _u ∈ good, 100 * (2 * typeCount) := by
      apply Finset.sum_le_sum
      intro u hu
      exact Nat.mul_le_mul_left 100
        (neighborIncidenceCount_le_two_mul_typeCount
          twistSample (lightLayerSet Delta w) u)
    _ = 200 * typeCount * good.card := by
      rw [Finset.sum_const_nat (fun _ _ => rfl)]
      ring
end QEC.Coding.FiberBundle.TwistGraph
