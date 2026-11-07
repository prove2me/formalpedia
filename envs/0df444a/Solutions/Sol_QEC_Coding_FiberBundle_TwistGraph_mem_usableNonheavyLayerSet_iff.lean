-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.mem_usableNonheavyLayerSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T07:52:59.948271+00:00
-- url     : https://prove2.me/submissions/b50bf3ed-f30b-4af6-b037-840d18f84438

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
    u ∈ usableNonheavyLayerSet Delta twistSample w ↔
      u ∈ nonheavyLayerSet Delta w ∧
        typeCount ≤
          5 * neighborIncidenceCount twistSample
            (nonheavyLayerSet Delta w) u := by
  classical
  simp only [usableNonheavyLayerSet, Finset.mem_filter]
