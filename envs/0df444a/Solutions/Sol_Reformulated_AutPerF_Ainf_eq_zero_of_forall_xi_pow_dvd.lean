-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.eq_zero_of_forall_xi_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:37:42.790745+00:00
-- url     : https://prove2.me/submissions/2c5bd2e8-264b-40eb-a117-b4cbcea2c26c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_eq_zero_of_forall_pow_dvd
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_xi
import Theorems.Thm_Reformulated_AutPerF_Ainf_p_dvd_iff
import Theorems.Thm_Reformulated_AutPerF_Ainf_coeff_zero_xi
import Theorems.Thm_Reformulated_AutPerF_Ainf_xi_pow_dvd_of_dvd_p_pow_mul
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
theorem _root_.solution (ϖ : PFlat p R) {x : Ainf p R}
    (h : ∀ n : ℕ, xi ϖ ^ n ∣ x) : x = 0 := by
  refine eq_zero_of_forall_pow_dvd (p : Ainf p R) fun k => ?_
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have h0 : PreTilt.untilt (x.coeff 0) = 0 := eq_zero_of_forall_pow_dvd (p : R) fun n => by
      have h1 : (xi ϖ).coeff 0 ^ n ∣ x.coeff 0 := by
        have := map_dvd (WittVector.constantCoeff (p := p) (R := Tilt p R)) (h n)
        rwa [map_pow] at this
      rw [coeff_zero_xi] at h1
      have h2 : ϖ.1 ^ n ∣ x.coeff 0 := (pow_dvd_pow_of_dvd (dvd_neg.2 dvd_rfl) n).trans h1
      have h3 := map_dvd PreTilt.untilt h2
      rwa [map_pow, ϖ.2] at h3
    obtain ⟨y, rfl⟩ := (p_dvd_iff x).2 ((Tilt.untilt_eq_zero_iff _).1 h0)
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih fun n =>
      xi_pow_dvd_of_dvd_p_pow_mul ϖ (k := 1) (by simpa using h n))
end Reformulated.AutPerF.Ainf
