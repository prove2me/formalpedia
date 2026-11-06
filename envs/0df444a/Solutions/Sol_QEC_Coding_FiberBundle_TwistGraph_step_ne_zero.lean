-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.step_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:46:53.269653+00:00
-- url     : https://prove2.me/submissions/ad6e1c30-a0f1-48e7-b34a-688c50d16b3b

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_step_val

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) :
    step sample τ ≠ 0 := by
  intro hzero
  have hval := congrArg ZMod.val hzero
  rw [step_val, ZMod.val_zero] at hval
  omega
end QEC.Coding.FiberBundle.TwistGraph
