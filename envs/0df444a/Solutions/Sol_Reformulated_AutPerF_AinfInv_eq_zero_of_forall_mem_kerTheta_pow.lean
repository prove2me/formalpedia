-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.eq_zero_of_forall_mem_kerTheta_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:47:42.051558+00:00
-- url     : https://prove2.me/submissions/9ba608a5-f8b8-4106-8332-4deb8a730343

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_eq_zero_of_forall_xi_pow_dvd
import Theorems.Thm_Reformulated_AutPerF_AinfInv_exists_p_pow_mul_eq
import Theorems.Thm_Reformulated_AutPerF_AinfInv_algebraMap_mem_kerTheta_pow_iff

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
open Reformulated.AutPerF.AinfInv
variable [IsDomain R]
variable [ValuationRing R]
variable [CharZero R]
namespace Reformulated.AutPerF.AinfInv
theorem _root_.solution (ϖ : PFlat p R) {x : AinfInv p R}
    (h : ∀ n : ℕ, x ∈ kerTheta p R ^ n) : x = 0 := by
  obtain ⟨k, a, e⟩ := exists_p_pow_mul_eq x
  have : a = 0 := Ainf.eq_zero_of_forall_xi_pow_dvd ϖ fun n =>
    (algebraMap_mem_kerTheta_pow_iff ϖ n a).1 (e ▸ Ideal.mul_mem_left _ _ (h n))
  rw [this, map_zero] at e
  exact (((isUnit_p (R := R) p).pow k).mul_right_eq_zero).1 e
end Reformulated.AutPerF.AinfInv
