-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.blockEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:41:32.151518+00:00
-- url     : https://prove2.me/submissions/93c523db-c15d-4a82-8047-186b9ab2fbb1

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    (ell : Nat) [NeZero ell]
    (uk : ZMod ell × Fin ell) :
    blockEquiv ell uk = blockPosition ell uk := by
  rfl
end QEC.Coding.FiberBundle.TwistGraph
