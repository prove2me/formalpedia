-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_horizontalComponent_negativeSlideCluster_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:16:44.398002+00:00
-- url     : https://prove2.me/submissions/71b7734a-a3c9-4568-ac7d-a494309b1164

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalClusterSubchain_isBinarySubword
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalComponent_negativeStepSlide_le

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
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    HammingWeight
        (horizontalComponent
          (negativeStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root))) ≤
      HammingWeight (horizontalComponent z) := by
  apply hammingWeight_horizontalComponent_negativeStepSlide_le
  exact horizontalClusterSubchain_isBinarySubword
    baseSample twistSample z root
end QEC.Coding.FiberBundle
