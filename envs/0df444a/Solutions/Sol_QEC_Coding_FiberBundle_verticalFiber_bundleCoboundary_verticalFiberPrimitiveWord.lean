-- Prove2me | solution 1 for QEC.Coding.FiberBundle.verticalFiber_bundleCoboundary_verticalFiberPrimitiveWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:07.026595+00:00
-- url     : https://prove2.me/submissions/9cf163ac-a813-443e-806a-324b222cc148

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberCoboundary_cycleFiberPrimitive
import Theorems.Thm_QEC_Coding_FiberBundle_sum_verticalFiber_eq_zero_of_cocycle
import Theorems.Thm_QEC_Coding_FiberBundle_verticalFiber_bundleCoboundary_fiberBundleData


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier)
    (a : Fin (3 * r)) :
    verticalFiber
        (bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample)
          (verticalFiberPrimitiveWord z)) a =
      verticalFiber z a := by
  rw [verticalFiber_bundleCoboundary_fiberBundleData]
  have hEll : 2 ≤ ell := by
    have hPred : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  have hCycle : 2 ≤ ell * ell := by nlinarith
  exact cycleFiberCoboundary_cycleFiberPrimitive
    (ell * ell) hCycle (verticalFiber z a)
    (sum_verticalFiber_eq_zero_of_cocycle
      baseSample twistSample hRank z hz a)
end QEC.Coding.FiberBundle
