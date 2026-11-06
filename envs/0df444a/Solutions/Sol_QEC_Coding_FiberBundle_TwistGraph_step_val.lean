-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.step_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:44:58.917926+00:00
-- url     : https://prove2.me/submissions/7aad61a5-a928-4fc0-ae85-efb8226f28eb

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
    (τ : Fin typeCount) :
    (step sample τ).val =
      (RandomTwist.typeTwist sample τ).val + 1 := by
  rw [step, ZMod.val_natCast_of_lt]
  have h :=
    (RandomTwist.typeTwist sample τ).isLt
  omega
end QEC.Coding.FiberBundle.TwistGraph
