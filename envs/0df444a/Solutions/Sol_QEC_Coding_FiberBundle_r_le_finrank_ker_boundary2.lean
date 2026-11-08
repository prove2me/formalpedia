-- Prove2me | solution 1 for QEC.Coding.FiberBundle.r_le_finrank_ker_boundary2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:07:55.539208+00:00
-- url     : https://prove2.me/submissions/df94e045-1e83-460e-ac52-7a5dbd266ae9

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_dimension_code_eq
import Theorems.Thm_QEC_Coding_FiberBundle_constantFiberTwoCycleLinearMap_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample) :
    r ≤ Module.finrank (ZMod 2)
      (LinearMap.ker
        (boundary2
          (RandomTwist.fiberBundleData baseSample twistSample))) := by
  calc
    r = Dimension (RandomBase.code baseSample) :=
      (RandomBase.dimension_code_eq baseSample hRank).symm
    _ = Module.finrank (ZMod 2)
        (RandomBase.code baseSample).carrier := rfl
    _ ≤ Module.finrank (ZMod 2)
        (LinearMap.ker
          (boundary2
            (RandomTwist.fiberBundleData baseSample twistSample))) :=
      LinearMap.finrank_le_finrank_of_injective
        (constantFiberTwoCycleLinearMap_injective
          baseSample twistSample)
end QEC.Coding.FiberBundle
