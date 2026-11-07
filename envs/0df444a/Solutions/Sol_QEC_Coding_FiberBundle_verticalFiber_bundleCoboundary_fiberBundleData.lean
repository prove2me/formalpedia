-- Prove2me | solution 1 for QEC.Coding.FiberBundle.verticalFiber_bundleCoboundary_fiberBundleData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:26:30.196978+00:00
-- url     : https://prove2.me/submissions/c1b9fd10-118a-4244-bde0-1fff116a6868

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_verticalFiber_bundleCoboundary

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
    (a : Fin (3 * r)) :
    verticalFiber
        (bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample) u) a =
      cycleFiberCoboundary (ell * ell) (c0Fiber u a) := by
  funext j
  rw [verticalFiber_bundleCoboundary]
  rfl
end QEC.Coding.FiberBundle
