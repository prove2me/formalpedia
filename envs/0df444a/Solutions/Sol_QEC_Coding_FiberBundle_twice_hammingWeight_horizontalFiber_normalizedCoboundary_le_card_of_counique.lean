-- Prove2me | solution 1 for QEC.Coding.FiberBundle.twice_hammingWeight_horizontalFiber_normalizedCoboundary_le_card_of_counique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:33:11.964433+00:00
-- url     : https://prove2.me/submissions/297ffb4a-d584-4701-97ba-8553fbeb5e6c

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_c0FibersNormalized_normalizeC0Fibers
import Theorems.Thm_QEC_Coding_FiberBundle_twice_hammingWeight_horizontalFiber_bundleCoboundary_le_card_of_counique

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
    (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample
      (c0Shadow (normalizeC0Fibers u))) :
    2 * HammingWeight
        (horizontalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (normalizeC0Fibers u)) b) ≤
      Fintype.card (ZMod (ell * ell)) := by
  exact
    twice_hammingWeight_horizontalFiber_bundleCoboundary_le_card_of_counique
      baseSample twistSample (normalizeC0Fibers u)
      (c0FibersNormalized_normalizeC0Fibers u) b hb
end QEC.Coding.FiberBundle
