-- Prove2me | solution 1 for QEC.Coding.FiberBundle.IsHorizontalWeightMinimal.normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:36:20.869492+00:00
-- url     : https://prove2.me/submissions/1942cd88-c1df-448e-9371-dbe0ce8f79d0

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
namespace IsHorizontalWeightMinimal
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hMinimal : IsHorizontalWeightMinimal baseSample twistSample x u) :
    IsHorizontalWeightMinimal baseSample twistSample
      (x + normalizationBaseShift baseSample u)
      (QEC.Coding.FiberBundle.normalizeC0Fibers u) := by
  intro v
  let weight := fun representative :
      Word (ZMod 2)
        (QubitIndex (Fin (3 * r)) (Fin (4 * r))
          (ZMod (ell * ell)) (ZMod (ell * ell))) =>
    HammingWeight (horizontalComponent representative)
  calc
    weight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell))
            (x + normalizationBaseShift baseSample u) +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (QEC.Coding.FiberBundle.normalizeC0Fibers u)) =
      weight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u) := by
        exact congrArg weight
          (horizontalBaseLift_add_bundleCoboundary_normalizeC0Fibers
            baseSample twistSample x u)
    _ ≤
      weight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (v + normalizationToggleWord u)) :=
        hMinimal (v + normalizationToggleWord u)
    _ =
      weight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell))
            (x + normalizationBaseShift baseSample u) +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) v) := by
        exact congrArg weight
          (horizontalBaseLift_add_bundleCoboundary_baseShift
            baseSample twistSample x u v).symm
end IsHorizontalWeightMinimal
end QEC.Coding.FiberBundle
