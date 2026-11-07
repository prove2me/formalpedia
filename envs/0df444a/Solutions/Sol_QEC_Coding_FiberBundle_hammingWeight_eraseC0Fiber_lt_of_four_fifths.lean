-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_eraseC0Fiber_lt_of_four_fifths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:36:25.088335+00:00
-- url     : https://prove2.me/submissions/c7b78aed-d57c-4aa5-bd70-9b4379194ee9

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_eq_horizontal_add_vertical
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalComponent_eraseC0Fiber_lt_of_four_fifths
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_verticalComponent_eraseC0Fiber_le

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
    (a : Fin (3 * r))
    (ha : a ∈ c0Shadow u)
    (hCounique :
      4 * RandomBase.checkDegree baseSample a <
        5 * RandomBase.couniqueDegree baseSample (c0Shadow u) a)
    (hDisjoint :
      ∀ b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u),
        x b = 0) :
    HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (eraseC0Fiber u a)) <
      HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u) := by
  rw [hammingWeight_eq_horizontal_add_vertical,
    hammingWeight_eq_horizontal_add_vertical]
  have hHorizontal :=
    hammingWeight_horizontalComponent_eraseC0Fiber_lt_of_four_fifths
      baseSample twistSample x u a ha hCounique hDisjoint
  have hVertical :=
    hammingWeight_verticalComponent_eraseC0Fiber_le
      baseSample twistSample x u a
  omega
end QEC.Coding.FiberBundle
