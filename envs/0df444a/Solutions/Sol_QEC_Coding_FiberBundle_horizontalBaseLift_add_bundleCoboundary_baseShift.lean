-- Prove2me | solution 1 for QEC.Coding.FiberBundle.horizontalBaseLift_add_bundleCoboundary_baseShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:33:07.157968+00:00
-- url     : https://prove2.me/submissions/cc63dd6d-eca2-4881-8a94-2a8817c0e852

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_bundleCoboundary_normalizationToggleWord_eq_horizontalBaseLift

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
    (u v : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) :
    horizontalBaseLift
          (baseZero := Fin (3 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell))
          (x + normalizationBaseShift baseSample u) +
        bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample) v =
      horizontalBaseLift
          (baseZero := Fin (3 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell)) x +
        bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample)
          (v + normalizationToggleWord u) := by
  have hCoboundaryAdd :
      bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample)
          (v + normalizationToggleWord u) =
        bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) v +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (normalizationToggleWord u) := by
    exact map_add
      (wordLinearMapTranspose
        (boundary1 (RandomTwist.fiberBundleData baseSample twistSample)))
      v (normalizationToggleWord u)
  rw [horizontalBaseLift_add]
  rw [hCoboundaryAdd]
  rw [bundleCoboundary_normalizationToggleWord_eq_horizontalBaseLift]
  abel
end QEC.Coding.FiberBundle
