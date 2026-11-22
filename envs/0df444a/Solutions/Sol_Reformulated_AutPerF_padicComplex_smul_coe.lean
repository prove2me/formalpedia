-- Prove2me | solution 1 for Reformulated.AutPerF.padicComplex_smul_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:10.342091+00:00
-- url     : https://prove2.me/submissions/9d472316-1429-4d70-b8b6-e928df922957

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
variable (p : ℕ) [Fact p.Prime]
namespace Reformulated.AutPerF
theorem _root_.solution {K : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
    [IsScalarTower ℚ_[p] K (PadicAlgCl p)] (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p)
    (x : PadicAlgCl p) : g • (x : ℂ_[p]) = (g x : PadicAlgCl p) :=
  (UniformSpace.Completion.coe_smul g x).symm
end Reformulated.AutPerF
