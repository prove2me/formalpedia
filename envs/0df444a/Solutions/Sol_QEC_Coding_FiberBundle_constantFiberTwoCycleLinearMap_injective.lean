-- Prove2me | solution 1 for QEC.Coding.FiberBundle.constantFiberTwoCycleLinearMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:00:55.400718+00:00
-- url     : https://prove2.me/submissions/2b229b8d-d9cd-4c3c-9270-7d45a2616c5e

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Function.Injective
      (constantFiberTwoCycleLinearMap baseSample twistSample) := by
  intro x y hxy
  apply Subtype.ext
  funext b
  have h := congrFun (congrArg Subtype.val hxy)
    (b, (0 : ZMod (ell * ell)))
  exact h
end QEC.Coding.FiberBundle
