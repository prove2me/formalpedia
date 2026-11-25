-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.associated_xi_omega
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:15:49.135942+00:00
-- url     : https://prove2.me/submissions/1ef1cbe6-ffaa-47ba-95c8-c6db57d6234e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Tilt_isUnit_iff_isUnit_coeff
import Theorems.Thm_Reformulated_AutPerF_Tilt_isUnit_iff_isUnit_untilt
import Theorems.Thm_Reformulated_AutPerF_Tilt_isUnit_iff_isUnit_coeff_zero
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_xi
import Theorems.Thm_Reformulated_AutPerF_Ainf_isUnit_iff_isUnit_coeff
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_eq_zero_iff
import Theorems.Thm_Reformulated_AutPerF_tateRoot_pow
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_omega
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_theta_eq_zero_iff
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
variable [ValuationRing R] [CharZero R]
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution (ϖ : PFlat p R) {ε : tateModule p R} (hε : IsPrimitive ε) :
    Associated (xi ϖ) (omega ε) := by
  obtain ⟨a, ha⟩ := (theta_eq_zero_iff ϖ _).1 (theta_omega hε)
  let ρ := IsLocalRing.residue (Tilt p R)
  have hc : CharP (IsLocalRing.ResidueField (Tilt p R)) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by rw [← map_natCast ρ, CharP.cast_eq_zero, map_zero])
  have h1 : ρ ϖ.1 = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Tilt.isUnit_iff_isUnit_untilt, ϖ.2]
    exact Fact.out
  have h2 : ρ (tateRoot ε) = 1 := by
    rw [← sub_eq_zero, ← map_one ρ, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h3 := hu.pow p
    rw [sub_pow_char, tateRoot_pow, one_pow, Tilt.isUnit_iff_isUnit_coeff_zero, map_sub,
      ← PreTilt.mk_untilt_eq_coeff_zero, show PreTilt.untilt ε.1 = 1 from ε.2, map_one, map_one,
      sub_self, ← map_zero (Ideal.Quotient.mk (span {(p : R)})),
      Tilt.isUnit_iff_isUnit_coeff] at h3
    exact not_isUnit_zero h3
  have h4 := congrArg (WittVector.map (p := p) ρ) ha
  simp only [omega, xi, map_sum, map_pow, map_mul, map_sub, map_natCast,
    WittVector.map_teichmuller, h1, h2, map_one, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, WittVector.teichmuller_zero, sub_zero] at h4
  have h5 : WittVector.map (p := p) ρ a = 1 :=
    mul_left_cancel₀ (WittVector.p_nonzero p _) (h4.symm.trans (mul_one _).symm)
  have h6 : ρ (a.coeff 0) = 1 := by
    rw [← WittVector.map_coeff, h5, WittVector.one_coeff_zero]
  have hu : IsUnit a := by
    rw [isUnit_iff_isUnit_coeff, ← IsLocalRing.residue_ne_zero_iff_isUnit]
    exact h6 ▸ one_ne_zero
  exact ⟨hu.unit, ha.symm⟩
end Reformulated.AutPerF.Ainf
