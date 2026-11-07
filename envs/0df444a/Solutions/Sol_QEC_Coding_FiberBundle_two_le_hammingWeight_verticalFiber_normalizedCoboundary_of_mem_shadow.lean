-- Prove2me | solution 1 for QEC.Coding.FiberBundle.two_le_hammingWeight_verticalFiber_normalizedCoboundary_of_mem_shadow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:36:08.656226+00:00
-- url     : https://prove2.me/submissions/3e865dfc-d171-401c-aa07-ecc0f5da842f

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_c0FibersNormalized_normalizeC0Fibers
import Theorems.Thm_QEC_Coding_FiberBundle_two_le_hammingWeight_verticalFiber_coboundary_of_mem_shadow_of_normalized

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
    (a : Fin (3 * r))
    (ha : a ∈ c0Shadow (normalizeC0Fibers u)) :
    2 ≤ HammingWeight
      (verticalFiber
        (bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample)
          (normalizeC0Fibers u)) a) := by
  exact
    two_le_hammingWeight_verticalFiber_coboundary_of_mem_shadow_of_normalized
      baseSample twistSample (normalizeC0Fibers u)
      (c0FibersNormalized_normalizeC0Fibers u) a ha
end QEC.Coding.FiberBundle
