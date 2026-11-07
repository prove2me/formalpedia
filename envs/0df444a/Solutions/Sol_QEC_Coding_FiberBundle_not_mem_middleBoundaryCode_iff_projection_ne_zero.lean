-- Prove2me | solution 1 for QEC.Coding.FiberBundle.not_mem_middleBoundaryCode_iff_projection_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:02.730092+00:00
-- url     : https://prove2.me/submissions/d363e816-3031-4b6e-87b1-e6133b2791a1

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_not_mem_middleBoundaryCode_of_projection_ne_zero
import Theorems.Thm_QEC_Coding_FiberBundle_mem_middleBoundaryCode_of_projection_eq_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier) :
    z ∉ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleBoundaryCode.carrier ↔
      homologyBaseProjection z ≠ 0 := by
  constructor
  · intro hzNontrivial hzProjection
    exact hzNontrivial
      (mem_middleBoundaryCode_of_projection_eq_zero
        baseSample twistSample hRank z hz hzProjection)
  · exact not_mem_middleBoundaryCode_of_projection_ne_zero
      baseSample twistSample z
end QEC.Coding.FiberBundle
