-- Prove2me | solution 1 for QEC.Coding.FiberBundle.oneStepSlide_add_boundary_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:02:25.203343+00:00
-- url     : https://prove2.me/submissions/36183749-663b-445d-9812-d4bff94d37fd

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives

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
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    oneStepSlide baseSample twistSample z h =
      z +
        boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (oneStepSlideTwoChain h) := by
  rfl
end QEC.Coding.FiberBundle
