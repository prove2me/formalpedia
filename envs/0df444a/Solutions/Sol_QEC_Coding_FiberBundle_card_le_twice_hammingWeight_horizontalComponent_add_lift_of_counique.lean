-- Prove2me | solution 1 for QEC.Coding.FiberBundle.card_le_twice_hammingWeight_horizontalComponent_add_lift_of_counique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:37:14.474077+00:00
-- url     : https://prove2.me/submissions/0c80f959-1eca-4c68-9faf-f18dd7fdc12d

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_card_le_twice_hammingWeight_horizontalFiber_add_lift_of_counique
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalFiber_le_horizontalComponent

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
    (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample
      (c0Shadow (normalizeC0Fibers u)))
    (hxb : x b ≠ 0) :
    Fintype.card (ZMod (ell * ell)) ≤
      2 * HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (normalizeC0Fibers u))) := by
  let representative :=
    horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell)) x +
      bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample)
        (normalizeC0Fibers u)
  have hfiber :
      Fintype.card (ZMod (ell * ell)) ≤
        2 * HammingWeight (horizontalFiber representative b) := by
    exact
      card_le_twice_hammingWeight_horizontalFiber_add_lift_of_counique
        baseSample twistSample x u b hb hxb
  have hsector :
      HammingWeight (horizontalFiber representative b) ≤
        HammingWeight (horizontalComponent representative) :=
    hammingWeight_horizontalFiber_le_horizontalComponent representative b
  exact hfiber.trans (Nat.mul_le_mul_left 2 hsector)
end QEC.Coding.FiberBundle
