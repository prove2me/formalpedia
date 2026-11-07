-- Prove2me | solution 1 for QEC.Coding.FiberBundle.fiberResidue_connection_onOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:33.601208+00:00
-- url     : https://prove2.me/submissions/97e55e87-eeb5-441b-806b-3099fcefd994

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_fiberResidue_multipleRotation_eq_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (b : Fin (4 * r)) (a : Fin (3 * r))
    (j : ZMod (ell * ell)) :
    fiberResidue ell
        ((((RandomTwist.fiberBundleData baseSample twistSample
          ).connection b a).onOne) j) =
      fiberResidue ell j := by
  change fiberResidue ell
    (j + multipleRotation ell
      (RandomTwist.connectionIndex twistSample b a)) =
    fiberResidue ell j
  rw [map_add]
  rw [fiberResidue_multipleRotation_eq_zero, add_zero]
end QEC.Coding.FiberBundle
