-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.mem_badNonheavyLayerSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T07:52:04.440125+00:00
-- url     : https://prove2.me/submissions/9c7b138b-88f1-4f1b-bf45-25e1491bc1fa

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
theorem solution
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ badNonheavyLayerSet Delta twistSample w ↔
      u ∈ nonheavyLayerSet Delta w ∧
        u ∉ usableNonheavyLayerSet Delta twistSample w := by
  classical
  simp only [badNonheavyLayerSet, Finset.mem_sdiff]
