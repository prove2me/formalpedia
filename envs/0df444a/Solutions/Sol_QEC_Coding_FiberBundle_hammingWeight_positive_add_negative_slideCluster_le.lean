-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_positive_add_negative_slideCluster_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:26:03.05149+00:00
-- url     : https://prove2.me/submissions/fc9fd704-fbf9-41e1-be97-dce791441607

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalComponent_slideCluster_le
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalComponent_negativeSlideCluster_le
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_verticalComponent_positive_add_negative_slideCluster
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_eq_horizontal_add_vertical


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
        (oneStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) +
      HammingWeight
        (negativeStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) ≤
      2 * HammingWeight z := by
  have hPositiveHorizontal :
      HammingWeight
          (horizontalComponent
            (oneStepSlide baseSample twistSample z
              (horizontalClusterSubchain
                baseSample twistSample z root))) ≤
        HammingWeight (horizontalComponent z) :=
    hammingWeight_horizontalComponent_slideCluster_le
      baseSample twistSample z root
  have hNegativeHorizontal :
      HammingWeight
          (horizontalComponent
            (negativeStepSlide baseSample twistSample z
              (horizontalClusterSubchain
                baseSample twistSample z root))) ≤
        HammingWeight (horizontalComponent z) :=
    hammingWeight_horizontalComponent_negativeSlideCluster_le
      baseSample twistSample z root
  have hVertical :
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
        2 * HammingWeight (verticalComponent z) :=
    hammingWeight_verticalComponent_positive_add_negative_slideCluster
      baseSample twistSample z hz root
  rw [hammingWeight_eq_horizontal_add_vertical,
    hammingWeight_eq_horizontal_add_vertical,
    hammingWeight_eq_horizontal_add_vertical]
  omega
end QEC.Coding.FiberBundle
