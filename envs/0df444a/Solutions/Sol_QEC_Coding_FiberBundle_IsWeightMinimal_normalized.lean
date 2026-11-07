-- Prove2me | solution 1 for QEC.Coding.FiberBundle.IsWeightMinimal.normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:36:21.61045+00:00
-- url     : https://prove2.me/submissions/63c09c0f-06d4-486f-816f-26218c337447

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalBaseLift_add_bundleCoboundary_normalizeC0Fibers
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalBaseLift_add_bundleCoboundary_baseShift

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
namespace IsWeightMinimal
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hMinimal : IsWeightMinimal baseSample twistSample x u) :
    IsWeightMinimal baseSample twistSample
      (x + normalizationBaseShift baseSample u)
      (normalizeC0Fibers u) := by
  intro v
  calc
    HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell))
            (x + normalizationBaseShift baseSample u) +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (normalizeC0Fibers u)) =
      HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u) := by
        exact congrArg HammingWeight
          (horizontalBaseLift_add_bundleCoboundary_normalizeC0Fibers
            baseSample twistSample x u)
    _ ≤
      HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (v + normalizationToggleWord u)) :=
        hMinimal (v + normalizationToggleWord u)
    _ =
      HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell))
            (x + normalizationBaseShift baseSample u) +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) v) := by
        exact congrArg HammingWeight
          (horizontalBaseLift_add_bundleCoboundary_baseShift
            baseSample twistSample x u v).symm
end IsWeightMinimal
end QEC.Coding.FiberBundle
