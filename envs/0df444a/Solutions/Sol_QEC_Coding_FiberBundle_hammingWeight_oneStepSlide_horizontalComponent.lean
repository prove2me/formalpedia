-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_oneStepSlide_horizontalComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:48:05.681781+00:00
-- url     : https://prove2.me/submissions/8c21e789-e57f-478a-a3f8-ea20c67ae6a3

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_translateBundleWord
import Theorems.Thm_QEC_Coding_FiberBundle_oneStepSlide_horizontalComponent_eq_translateBundleWord

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
        ).middleCycleCode.carrier) :
    HammingWeight
        (oneStepSlide baseSample twistSample z
          (horizontalComponent z)) =
      HammingWeight z := by
  rw [oneStepSlide_horizontalComponent_eq_translateBundleWord
    baseSample twistSample z hz]
  exact hammingWeight_translateBundleWord (ell * ell) 1 z
end QEC.Coding.FiberBundle
