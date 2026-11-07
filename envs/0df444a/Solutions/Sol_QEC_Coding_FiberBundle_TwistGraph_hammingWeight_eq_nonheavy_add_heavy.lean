-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.hammingWeight_eq_nonheavy_add_heavy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:57:53.573604+00:00
-- url     : https://prove2.me/submissions/994578b8-009e-4fe6-8456-c80a992253b7

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_nonheavyLayerSet_union_heavyLayerSet
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_disjoint_nonheavyLayerSet_heavyLayerSet
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hammingWeight_eq_sum_layerWord


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    HammingWeight w =
      (∑ u ∈ nonheavyLayerSet Delta w,
        HammingWeight (layerWord w u)) +
      (∑ u ∈ heavyLayerSet Delta w,
        HammingWeight (layerWord w u)) := by
  rw [hammingWeight_eq_sum_layerWord]
  rw [← nonheavyLayerSet_union_heavyLayerSet Delta w]
  exact Finset.sum_union
    (disjoint_nonheavyLayerSet_heavyLayerSet Delta w)
end QEC.Coding.FiberBundle.TwistGraph
