-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HHO20DistanceBalancing.hho20FiberLength_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:41:34.345301+00:00
-- url     : https://prove2.me/submissions/293a53ea-bb21-49be-a115-4f1dad9eb9f4

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
universe u
namespace QEC.Coding.FiberBundle.HHO20DistanceBalancing
theorem _root_.solution (s : Nat) :
    RandomPartition.hho20FiberLength (2 * s) =
      RandomPartition.hho20FiberLength s ^ 2 := by
  unfold RandomPartition.hho20FiberLength
  rw [show 2 * s = s * 2 by omega, pow_mul]
end QEC.Coding.FiberBundle.HHO20DistanceBalancing
