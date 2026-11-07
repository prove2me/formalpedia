-- Prove2me | solution 1 for QEC.Coding.FiberBundle.verticalComponent_add_primitiveCoboundary_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:56:22.443236+00:00
-- url     : https://prove2.me/submissions/938b93a9-2ac2-442d-a4a2-5cea0367235c

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_verticalFiber_bundleCoboundary_verticalFiberPrimitiveWord

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
    verticalComponent
        (z +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (verticalFiberPrimitiveWord z)) = 0 := by
  funext aj
  rcases aj with ⟨a, j⟩
  change z (Sum.inr (a, j)) +
    bundleCoboundary
      (RandomTwist.fiberBundleData baseSample twistSample)
      (verticalFiberPrimitiveWord z) (Sum.inr (a, j)) = 0
  have hFiber :=
    congrFun
      (verticalFiber_bundleCoboundary_verticalFiberPrimitiveWord
        baseSample twistSample hRank z hz a) j
  change
    bundleCoboundary
      (RandomTwist.fiberBundleData baseSample twistSample)
      (verticalFiberPrimitiveWord z) (Sum.inr (a, j)) =
        z (Sum.inr (a, j)) at hFiber
  rw [hFiber]
  calc
    z (Sum.inr (a, j)) + z (Sum.inr (a, j)) =
        z (Sum.inr (a, j)) + (-z (Sum.inr (a, j))) := by
      rw [ZMod.neg_eq_self_mod_two]
    _ = 0 := add_neg_cancel _
end QEC.Coding.FiberBundle
