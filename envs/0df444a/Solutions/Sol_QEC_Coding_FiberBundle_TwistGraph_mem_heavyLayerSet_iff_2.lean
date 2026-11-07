-- Prove2me | solution 2 for QEC.Coding.FiberBundle.TwistGraph.mem_heavyLayerSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T07:52:02.461921+00:00
-- url     : https://prove2.me/submissions/5f4de396-2464-47da-b8eb-88f0e54bc577

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
    u ∈ heavyLayerSet Delta w ↔
      4 * (4 * r) ≤ Delta * HammingWeight (layerWord w u) := by
  classical
  simp only [heavyLayerSet, Finset.mem_filter, Finset.mem_univ, true_and]
