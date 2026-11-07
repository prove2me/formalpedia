-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.mem_nonheavyLayerSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T07:52:03.152247+00:00
-- url     : https://prove2.me/submissions/bbb2a5e0-784a-4f30-a455-3653c99b7a0c

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
theorem solution
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ nonheavyLayerSet Delta w ↔
      Delta * HammingWeight (layerWord w u) < 4 * (4 * r) := by
  classical
  simp only [nonheavyLayerSet, Finset.mem_filter, Finset.mem_univ, true_and]
