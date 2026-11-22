-- Prove2me | solution 1 for Reformulated.AutPerF.CK.smul_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:55.772798+00:00
-- url     : https://prove2.me/submissions/ca8ab27e-8ad6-4086-bcdb-d1bdac621db6

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
namespace CK
theorem _root_.solution (g : GalK K) (x : AlgCl K) : g • (x : CK K) = (g x : AlgCl K) :=
  (UniformSpace.Completion.coe_smul g x).symm
end CK
end Reformulated.AutPerF
