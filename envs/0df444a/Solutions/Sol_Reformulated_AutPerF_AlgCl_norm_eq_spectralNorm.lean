-- Prove2me | solution 1 for Reformulated.AutPerF.AlgCl.norm_eq_spectralNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:10.381753+00:00
-- url     : https://prove2.me/submissions/453c4bef-0ab5-450d-8c68-865054a51c36

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
open Reformulated.AutPerF.AlgCl
namespace Reformulated.AutPerF.AlgCl
theorem _root_.solution (x : AlgCl K) : ‖x‖ = spectralNorm K (AlgCl K) x := rfl
end Reformulated.AutPerF.AlgCl
