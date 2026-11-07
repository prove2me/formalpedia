-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_verticalComponent_positive_add_negative_slideCluster
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:23:42.131523+00:00
-- url     : https://prove2.me/submissions/81d29b16-f48f-4856-b844-afeed2d020a9

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_verticalFiber_positive_add_negative_slideCluster
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_verticalComponent_eq_sum_fibers


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
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    HammingWeight
        (verticalComponent
          (oneStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root))) +
      HammingWeight
        (verticalComponent
          (negativeStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root))) =
      2 * HammingWeight (verticalComponent z) := by
  rw [hammingWeight_verticalComponent_eq_sum_fibers,
    hammingWeight_verticalComponent_eq_sum_fibers,
    hammingWeight_verticalComponent_eq_sum_fibers,
    ← Finset.sum_add_distrib]
  calc
    (∑ a : Fin (3 * r),
      (HammingWeight
          (verticalFiber
            (oneStepSlide baseSample twistSample z
              (horizontalClusterSubchain
                baseSample twistSample z root)) a) +
        HammingWeight
          (verticalFiber
            (negativeStepSlide baseSample twistSample z
              (horizontalClusterSubchain
                baseSample twistSample z root)) a))) =
      ∑ a : Fin (3 * r),
        2 * HammingWeight (verticalFiber z a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact
            hammingWeight_verticalFiber_positive_add_negative_slideCluster
              baseSample twistSample z hz root a
    _ = 2 * ∑ a : Fin (3 * r),
        HammingWeight (verticalFiber z a) := by
          rw [Finset.mul_sum]
end QEC.Coding.FiberBundle
