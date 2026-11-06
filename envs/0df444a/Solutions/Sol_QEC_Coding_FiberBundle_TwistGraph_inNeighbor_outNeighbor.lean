-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.inNeighbor_outNeighbor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:41:54.014732+00:00
-- url     : https://prove2.me/submissions/326eec3f-e1d9-4c6e-a856-e1e3a32bc623

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) (u : ZMod ell) :
    inNeighbor sample τ (outNeighbor sample τ u) = u := by
  exact (typeTranslation sample τ).symm_apply_apply u
end QEC.Coding.FiberBundle.TwistGraph
