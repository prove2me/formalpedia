-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_globalSlideIterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:15:32.2082+00:00
-- url     : https://prove2.me/submissions/38bb0690-d9c0-4c63-866c-826ab794ef02

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_translateBundleWord
import Theorems.Thm_QEC_Coding_FiberBundle_globalSlideIterate_eq_translateBundleWord

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
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (k : Nat) :
    HammingWeight (globalSlideIterate baseSample twistSample z k) =
      HammingWeight z := by
  rw [globalSlideIterate_eq_translateBundleWord
    baseSample twistSample z hz k]
  exact hammingWeight_translateBundleWord
    (ell * ell) (k : ZMod (ell * ell)) z
end QEC.Coding.FiberBundle
