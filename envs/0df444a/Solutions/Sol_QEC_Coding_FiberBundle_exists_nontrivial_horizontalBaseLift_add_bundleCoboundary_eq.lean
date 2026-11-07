-- Prove2me | solution 1 for QEC.Coding.FiberBundle.exists_nontrivial_horizontalBaseLift_add_bundleCoboundary_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:10:09.866583+00:00
-- url     : https://prove2.me/submissions/af3b930d-fc82-4159-9fb0-e2f2140ecdea

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_exists_horizontalBaseLift_add_bundleCoboundary_eq_of_cocycle
import Theorems.Thm_QEC_Coding_FiberBundle_isNontrivialBaseCohomology_of_decomposition

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier)
    (hzNontrivial :
      z ∉ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).firstCoboundaryCheckCode.carrier) :
    ∃ x : Word (ZMod 2) (Fin (4 * r)),
      IsNontrivialBaseCohomology baseSample x ∧
      ∃ u : Word (ZMod 2)
        (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
        z =
          horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u := by
  rcases exists_horizontalBaseLift_add_bundleCoboundary_eq_of_cocycle
      baseSample twistSample hRank z hz with ⟨x, u, hDecomposition⟩
  refine ⟨x, ?_, u, hDecomposition⟩
  exact isNontrivialBaseCohomology_of_decomposition
    baseSample twistSample z x u hDecomposition hzNontrivial
end QEC.Coding.FiberBundle
