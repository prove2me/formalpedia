-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_verticalComponent_eraseC0Fiber_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:33:38.406565+00:00
-- url     : https://prove2.me/submissions/3ab70b12-69f4-4f35-902d-2d9e4acb1c6b

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_verticalComponent_eq_sum_fibers
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_verticalFiber_bundleCoboundary_eraseC0Fiber_le

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
        (verticalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (eraseC0Fiber u a))) ≤
      HammingWeight
        (verticalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u)) := by
  rw [verticalComponent_horizontalBaseLift_add,
    verticalComponent_horizontalBaseLift_add,
    hammingWeight_verticalComponent_eq_sum_fibers,
    hammingWeight_verticalComponent_eq_sum_fibers]
  exact Finset.sum_le_sum fun a' _ =>
    hammingWeight_verticalFiber_bundleCoboundary_eraseC0Fiber_le
      baseSample twistSample u a a'
end QEC.Coding.FiberBundle
