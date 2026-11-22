-- Prove2me | solution 1 for Reformulated.AutPerF.CK.smul_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:26.442862+00:00
-- url     : https://prove2.me/submissions/333c080b-396f-4350-ad04-c60faa8723ef

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_UniformContinuousConstSMulOfIsIsometricSMul
import Theorems.Thm_Reformulated_AutPerF_CK_smul_coe

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
namespace CK
theorem _root_.solution (g : GalK K) (x : K) :
    g • algebraMap K (CK K) x = algebraMap K (CK K) x := by
  change g • ((algebraMap K (AlgCl K) x : AlgCl K) : CK K) = (algebraMap K (AlgCl K) x : AlgCl K)
  rw [CK.smul_coe, AlgEquiv.commutes]
end CK
end Reformulated.AutPerF
