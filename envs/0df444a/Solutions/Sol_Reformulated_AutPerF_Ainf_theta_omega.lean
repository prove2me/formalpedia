-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.theta_omega
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:35.113049+00:00
-- url     : https://prove2.me/submissions/eb243ebf-37d8-4b20-aa94-b6fc5021a20c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_omega_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Ainf
variable [IsDomain R]
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution {ε : tateModule p R} (hε : IsPrimitive ε) : theta p R (omega ε) = 0 := by
  have h := congrArg (theta p R) (omega_mul ε)
  rw [map_mul, map_sub, map_sub, map_one, theta_teich, theta_teich,
    show PreTilt.untilt ε.1 = 1 from ε.2, sub_self, mul_eq_zero] at h
  exact h.resolve_right (sub_ne_zero.2 hε)
end Reformulated.AutPerF.Ainf
