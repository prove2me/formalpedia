-- Prove2me | solution 1 for QEC.Coding.FiberBundle.not_mem_middleBoundaryCode_of_projection_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:06:21.769616+00:00
-- url     : https://prove2.me/submissions/1f21ba85-a60c-44d8-ad2f-f6d6978f67df

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_boundary2_fiberBundleData_eq_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hzProjection : homologyBaseProjection z ≠ 0) :
    z ∉ (chainComplex
      (RandomTwist.fiberBundleData baseSample twistSample)
      ).middleBoundaryCode.carrier := by
  intro hzBoundary
  rcases ((chainComplex
    (RandomTwist.fiberBundleData baseSample twistSample)
    ).mem_middleBoundaryCode_iff z).1 hzBoundary with ⟨c, rfl⟩
  exact hzProjection
    (homologyBaseProjection_boundary2_fiberBundleData_eq_zero
      baseSample twistSample c)
end QEC.Coding.FiberBundle
