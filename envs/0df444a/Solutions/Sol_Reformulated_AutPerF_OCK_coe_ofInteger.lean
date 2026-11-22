-- Prove2me | solution 1 for Reformulated.AutPerF.OCK.coe_ofInteger
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:44.94963+00:00
-- url     : https://prove2.me/submissions/294c6d73-f0a2-424b-8f1f-661da77f8a97

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_UniformContinuousConstSMulOfIsIsometricSMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal Filter Topology
open Reformulated Reformulated.AutPerF
universe u v
variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
namespace Reformulated.AutPerF
namespace OCK
theorem _root_.solution (x : unitBall K) :
    (OCK.ofInteger K x : CK K) = algebraMap K (CK K) x := rfl
end OCK
end Reformulated.AutPerF
