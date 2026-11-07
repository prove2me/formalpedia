-- Prove2me | solution 1 for QEC.Coding.FiberBundle.exists_slideCluster_direction_hammingWeight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:03:22.657172+00:00
-- url     : https://prove2.me/submissions/bead06d0-4534-4233-a78e-fbc8175bdf70

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
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    HammingWeight
        (oneStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) ≤ HammingWeight z ∨
      HammingWeight
        (negativeStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) ≤ HammingWeight z := by
  have h :=
    hammingWeight_positive_add_negative_slideCluster_le
      baseSample twistSample z hz root
  omega
end QEC.Coding.FiberBundle
