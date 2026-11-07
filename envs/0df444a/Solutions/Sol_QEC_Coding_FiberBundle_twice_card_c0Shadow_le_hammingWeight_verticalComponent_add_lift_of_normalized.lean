-- Prove2me | solution 1 for QEC.Coding.FiberBundle.twice_card_c0Shadow_le_hammingWeight_verticalComponent_add_lift_of_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:39:35.111545+00:00
-- url     : https://prove2.me/submissions/fa72e4e2-5f7c-4015-87d6-78ff79d19f40

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_twice_card_c0Shadow_le_hammingWeight_verticalComponent_coboundary_of_normalized

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
    (hu : C0FibersNormalized u) :
    2 * (c0Shadow u).card ≤
      HammingWeight
        (verticalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u)) := by
  rw [verticalComponent_horizontalBaseLift_add]
  exact
    twice_card_c0Shadow_le_hammingWeight_verticalComponent_coboundary_of_normalized
      baseSample twistSample u hu
end QEC.Coding.FiberBundle
