-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.sum_incidentViolationCount_eq_nonheavy_add_heavy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:58:40.54136+00:00
-- url     : https://prove2.me/submissions/97ee9908-0d48-4f85-9848-cec64fcf8eac

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_nonheavyLayerSet_union_heavyLayerSet
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_disjoint_nonheavyLayerSet_heavyLayerSet

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    (∑ u : ZMod ell,
      incidentViolationCount baseSample twistSample w u) =
      (∑ u ∈ nonheavyLayerSet Delta w,
        incidentViolationCount baseSample twistSample w u) +
      (∑ u ∈ heavyLayerSet Delta w,
        incidentViolationCount baseSample twistSample w u) := by
  rw [← nonheavyLayerSet_union_heavyLayerSet Delta w]
  exact Finset.sum_union
    (disjoint_nonheavyLayerSet_heavyLayerSet Delta w)
end QEC.Coding.FiberBundle.TwistGraph
