-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.mem_badHeavyLayerSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T07:52:03.848073+00:00
-- url     : https://prove2.me/submissions/435706db-b7e1-4bc7-8786-82b94415a0e5

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
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
    u ∈ badHeavyLayerSet Delta twistSample w ↔
      u ∈ heavyLayerSet Delta w ∧
        u ∉ usableHeavyLayerSet Delta twistSample w := by
  classical
  simp only [badHeavyLayerSet, Finset.mem_sdiff]
