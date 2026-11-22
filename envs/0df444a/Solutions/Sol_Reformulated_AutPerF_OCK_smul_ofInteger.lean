-- Prove2me | solution 1 for Reformulated.AutPerF.OCK.smul_ofInteger
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:37.781995+00:00
-- url     : https://prove2.me/submissions/a2a42bd0-cf97-4ab1-be38-74f822fbe38b

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_UniformContinuousConstSMulOfIsIsometricSMul
import Theorems.Thm_Reformulated_AutPerF_OCK_coe_ofInteger
import Theorems.Thm_Reformulated_AutPerF_CK_smul_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.OCK.coe_ofInteger

set_option autoImplicit false
noncomputable section
open Ideal Filter Topology
open Reformulated Reformulated.AutPerF
universe u v
variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
namespace Reformulated.AutPerF
namespace OCK
theorem _root_.solution (g : GalK K) (x : unitBall K) :
    g • OCK.ofInteger K x = OCK.ofInteger K x := Subtype.ext (CK.smul_algebraMap K g x)
end OCK
end Reformulated.AutPerF
