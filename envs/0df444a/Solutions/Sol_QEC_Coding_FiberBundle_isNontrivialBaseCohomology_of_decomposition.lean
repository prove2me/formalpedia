-- Prove2me | solution 1 for QEC.Coding.FiberBundle.isNontrivialBaseCohomology_of_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:35:26.191966+00:00
-- url     : https://prove2.me/submissions/0aac5905-2c25-4eb8-9b82-e9ba0cd4e6f2

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_bundleCoboundary_constantFiberWord_eq_horizontalBaseLift

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hDecomposition :
      z =
        horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u)
    (hzNontrivial :
      z ∉ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).firstCoboundaryCheckCode.carrier) :
    IsNontrivialBaseCohomology baseSample x := by
  intro t hxt
  apply hzNontrivial
  rw [hDecomposition, hxt,
    ← bundleCoboundary_constantFiberWord_eq_horizontalBaseLift
      baseSample twistSample t]
  rw [ChainComplexData.mem_firstCoboundaryCheckCode_iff]
  refine ⟨constantFiberWord
      (fiberZero := ZMod (ell * ell)) t + u, ?_⟩
  exact map_add
    (wordLinearMapTranspose
      (boundary1
        (RandomTwist.fiberBundleData baseSample twistSample)))
    (constantFiberWord (fiberZero := ZMod (ell * ell)) t) u
end QEC.Coding.FiberBundle
