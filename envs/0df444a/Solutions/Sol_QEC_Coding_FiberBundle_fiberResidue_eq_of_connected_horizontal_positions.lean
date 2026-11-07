-- Prove2me | solution 1 for QEC.Coding.FiberBundle.fiberResidue_eq_of_connected_horizontal_positions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:56:23.174339+00:00
-- url     : https://prove2.me/submissions/0d6278fc-5095-4cd4-bc23-d0379ec16b66

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_fiberResidue_connection_onZero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (b b' : Fin (4 * r)) (a : Fin (3 * r))
    (i i' : ZMod (ell * ell))
    (hMeet :
      ((RandomTwist.fiberBundleData baseSample twistSample
        ).connection b a).onZero i =
      ((RandomTwist.fiberBundleData baseSample twistSample
        ).connection b' a).onZero i') :
    fiberResidue ell i = fiberResidue ell i' := by
  have h := congrArg (fiberResidue ell) hMeet
  rw [fiberResidue_connection_onZero
      baseSample twistSample b a i,
    fiberResidue_connection_onZero
      baseSample twistSample b' a i'] at h
  exact h
end QEC.Coding.FiberBundle
