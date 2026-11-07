-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_horizontalComponent_eraseC0Fiber_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:00:10.611791+00:00
-- url     : https://prove2.me/submissions/f681f719-8d0e-44f0-84b9-43f5096d5957

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalBaseLift_add_bundleCoboundary_eraseC0Fiber
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalComponent_bundleCoboundary_eraseC0FiberCorrection
import Theorems.Thm_QEC_Coding_HammingWeight_add_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r)) :
    HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (eraseC0Fiber u a))) ≤
      HammingWeight
          (horizontalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample) u)) +
        RandomBase.checkDegree baseSample a * HammingWeight (c0Fiber u a) := by
  rw [horizontalBaseLift_add_bundleCoboundary_eraseC0Fiber,
    horizontalComponent_add]
  refine (HammingWeight_add_le _ _).trans_eq ?_
  rw [hammingWeight_horizontalComponent_bundleCoboundary_eraseC0FiberCorrection]
end QEC.Coding.FiberBundle
