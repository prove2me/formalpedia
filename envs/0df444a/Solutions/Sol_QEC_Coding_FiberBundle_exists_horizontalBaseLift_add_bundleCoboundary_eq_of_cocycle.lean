-- Prove2me | solution 1 for QEC.Coding.FiberBundle.exists_horizontalBaseLift_add_bundleCoboundary_eq_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:08:23.719727+00:00
-- url     : https://prove2.me/submissions/6bc6cfab-3d46-47ea-9d70-59afcf635600

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_exists_add_primitiveCoboundary_eq_horizontalBaseLift

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
        ).middleCocycleCode.carrier) :
    ∃ x : Word (ZMod 2) (Fin (4 * r)),
      ∃ u : Word (ZMod 2)
        (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
        z =
          horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u := by
  let u := verticalFiberPrimitiveWord z
  rcases exists_add_primitiveCoboundary_eq_horizontalBaseLift
      baseSample twistSample hRank z hz with ⟨x, hCleared⟩
  refine ⟨x, u, ?_⟩
  rw [← hCleared]
  funext q
  change z q = (z q + bundleCoboundary
    (RandomTwist.fiberBundleData baseSample twistSample) u q) +
      bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample) u q
  let w :=
    bundleCoboundary
      (RandomTwist.fiberBundleData baseSample twistSample) u q
  have hww : w + w = 0 := by
    calc
      w + w = w + (-w) := by rw [ZMod.neg_eq_self_mod_two]
      _ = 0 := add_neg_cancel w
  calc
    z q = z q + 0 := by rw [add_zero]
    _ = (z q + w) + w := by rw [add_assoc, hww, add_zero]
end QEC.Coding.FiberBundle
