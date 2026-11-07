-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_positive_eq_and_negative_eq_of_homologyClassWeightMinimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:29:44.693205+00:00
-- url     : https://prove2.me/submissions/495dd65f-452a-44f1-9b84-b0c835ad07db

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_positive_add_negative_slideCluster_le

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
    (hMinimal :
      IsHomologyClassWeightMinimal baseSample twistSample z)
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    HammingWeight
        (oneStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) =
        HammingWeight z ∧
    HammingWeight
        (negativeStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) =
        HammingWeight z := by
  have hPositiveLower :
      HammingWeight z ≤
        HammingWeight
          (oneStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root)) := by
    exact hMinimal
      (oneStepSlideTwoChain
        (horizontalClusterSubchain
          baseSample twistSample z root))
  have hNegativeLower :
      HammingWeight z ≤
        HammingWeight
          (negativeStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root)) := by
    exact hMinimal
      (negativeStepSlideTwoChain (ell * ell)
        (horizontalClusterSubchain
          baseSample twistSample z root))
  have hSum :=
    hammingWeight_positive_add_negative_slideCluster_le
      baseSample twistSample z hz root
  constructor <;> omega
end QEC.Coding.FiberBundle
