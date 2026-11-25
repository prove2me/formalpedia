-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.exists_teich_sub_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:27:14.545962+00:00
-- url     : https://prove2.me/submissions/4298ab59-4474-4297-b4e7-1dbe71da968c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_omega_mul
import Theorems.Thm_Reformulated_AutPerF_Ainf_associated_xi_omega

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
variable [ValuationRing R] [CharZero R]
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution (ϖ : PFlat p R) {ε : tateModule p R} (hε : IsPrimitive ε) :
    ∃ b, teich p ε.1 - 1 = xi ϖ * b ∧ theta p R b ≠ 0 := by
  obtain ⟨u, hu⟩ := associated_xi_omega ϖ hε
  refine ⟨u * (teich p (tateRoot ε) - 1), by rw [← mul_assoc, hu, omega_mul], ?_⟩
  rw [map_mul, map_sub, map_one, theta_teich]
  exact mul_ne_zero (u.isUnit.map _).ne_zero (sub_ne_zero.2 hε)
end Reformulated.AutPerF.Ainf
