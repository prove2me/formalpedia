-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.mem_usableHeavyLayerSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T07:52:05.099485+00:00
-- url     : https://prove2.me/submissions/148b2c68-22a4-4cd7-b9a5-2abf65975575

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
    u ∈ usableHeavyLayerSet Delta twistSample w ↔
      u ∈ heavyLayerSet Delta w ∧
        98 * typeCount ≤
          100 * (twoSidedLightTypeSet Delta twistSample w u).card := by
  classical
  simp only [usableHeavyLayerSet, Finset.mem_filter]
