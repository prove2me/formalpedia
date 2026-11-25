-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.xi_pow_dvd_of_dvd_p_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:28:11.063538+00:00
-- url     : https://prove2.me/submissions/ee95bb3e-693b-4cda-8a1d-bb041eb0b3b2

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_xi
import Theorems.Thm_Reformulated_AutPerF_Ainf_xi_ne_zero
import Theorems.Thm_Reformulated_AutPerF_Ainf_xi_dvd_of_dvd_p_pow_mul
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap


attribute [local simp] Reformulated.AutPerF.Ainf.theta_xi

set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Ainf
variable [IsDomain R]
variable [ValuationRing R]
variable [CharZero R]
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution (ϖ : PFlat p R) {n k : ℕ} {x : Ainf p R}
    (h : xi ϖ ^ n ∣ (p : Ainf p R) ^ k * x) : xi ϖ ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨y, rfl⟩ := xi_dvd_of_dvd_p_pow_mul ϖ ((dvd_pow_self _ n.succ_ne_zero).trans h)
    rw [pow_succ', mul_left_comm, mul_dvd_mul_iff_left (xi_ne_zero ϖ)] at h
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih h)
end Reformulated.AutPerF.Ainf
