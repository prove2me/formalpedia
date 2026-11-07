-- Prove2me | solution 1 for QEC.Coding.FiberBundle.large_shadow_vertical_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:00:26.605246+00:00
-- url     : https://prove2.me/submissions/72cc5a9e-8e25-4730-97f3-94100450ac3b

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_twice_card_c0Shadow_le_hammingWeight_verticalComponent_add_lift

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hLarge :
      3 * r < 100000 * Delta * (c0Shadow (normalizeC0Fibers u)).card) :
    6 * r <
      100000 * Delta *
        HammingWeight
          (verticalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample)
                (normalizeC0Fibers u))) := by
  have hvertical :=
    twice_card_c0Shadow_le_hammingWeight_verticalComponent_add_lift
      baseSample twistSample x u
  nlinarith
end QEC.Coding.FiberBundle
