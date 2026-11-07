-- Prove2me | solution 1 for QEC.Coding.FiberBundle.fiberResidue_connection_onZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:28.757872+00:00
-- url     : https://prove2.me/submissions/88b0b129-e676-4729-b7db-03ca0d7c81ee

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
    (i : ZMod (ell * ell)) :
    fiberResidue ell
        ((((RandomTwist.fiberBundleData baseSample twistSample
          ).connection b a).onZero) i) =
      fiberResidue ell i := by
  change fiberResidue ell
    (i + multipleRotation ell
      (RandomTwist.connectionIndex twistSample b a)) =
    fiberResidue ell i
  rw [map_add]
  rw [fiberResidue_multipleRotation_eq_zero, add_zero]
end QEC.Coding.FiberBundle
