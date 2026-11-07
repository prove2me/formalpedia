-- Prove2me | solution 1 for QEC.Coding.FiberBundle.card_le_twice_hammingWeight_horizontalFiber_add_lift_of_counique_of_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:20:00.905729+00:00
-- url     : https://prove2.me/submissions/ec3f7379-2ead-4604-9124-1ba6de5870d9

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_card_le_twice_hammingWeight_binaryComplement
import Theorems.Thm_QEC_Coding_FiberBundle_twice_hammingWeight_horizontalFiber_bundleCoboundary_le_card_of_counique
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_zmod2_eq_one_of_ne_zero


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
    (hu : C0FibersNormalized u)
    (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u))
    (hxb : x b ≠ 0) :
    Fintype.card (ZMod (ell * ell)) ≤
      2 * HammingWeight
        (horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) b) := by
  let f :=
    horizontalFiber
      (bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample) u) b
  have hfLight : 2 * HammingWeight f ≤ Fintype.card (ZMod (ell * ell)) := by
    exact
      twice_hammingWeight_horizontalFiber_bundleCoboundary_le_card_of_counique
        baseSample twistSample u hu b hb
  have hxbOne : x b = 1 :=
    RandomBase.zmod2_eq_one_of_ne_zero (x b) hxb
  have hfiber :
      horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) b =
        binaryComplement f := by
    funext i
    change x b + f i = 1 + f i
    rw [hxbOne]
  rw [hfiber]
  exact card_le_twice_hammingWeight_binaryComplement f hfLight
end QEC.Coding.FiberBundle
