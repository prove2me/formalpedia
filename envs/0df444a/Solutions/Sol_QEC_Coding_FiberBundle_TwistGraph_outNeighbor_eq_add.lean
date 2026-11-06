-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.outNeighbor_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:41:20.931073+00:00
-- url     : https://prove2.me/submissions/5444164c-2337-43f5-aea8-32dfa00e42ca

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
    outNeighbor sample τ u = u + step sample τ := by
  rfl
end QEC.Coding.FiberBundle.TwistGraph
