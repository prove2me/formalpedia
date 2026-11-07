-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_horizontalFiber_bundleCoboundary_eraseC0FiberCorrection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:03:15.917965+00:00
-- url     : https://prove2.me/submissions/ec51f425-904e-4065-9137-8027a27dfb3b

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_reindexWord
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalFiber_bundleCoboundary_eraseC0FiberCorrection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r)) (b : Fin (4 * r)) :
    HammingWeight
        (horizontalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (eraseC0FiberCorrection u a)) b) =
      if baseSample (a, b) then HammingWeight (c0Fiber u a) else 0 := by
  rw [horizontalFiber_bundleCoboundary_eraseC0FiberCorrection]
  by_cases hab : baseSample (a, b)
  · rw [if_pos hab, if_pos hab, hammingWeight_reindexWord]
  · rw [if_neg hab, if_neg hab, HammingWeight_zero]
end QEC.Coding.FiberBundle
