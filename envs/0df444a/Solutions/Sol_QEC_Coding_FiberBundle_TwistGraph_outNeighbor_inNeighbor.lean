-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.outNeighbor_inNeighbor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:42:09.157526+00:00
-- url     : https://prove2.me/submissions/2518df91-2202-44d1-b100-56631df14c9f

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
    outNeighbor sample τ (inNeighbor sample τ u) = u := by
  exact (typeTranslation sample τ).apply_symm_apply u
end QEC.Coding.FiberBundle.TwistGraph
