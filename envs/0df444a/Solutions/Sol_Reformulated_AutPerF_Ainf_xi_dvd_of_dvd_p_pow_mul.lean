-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.xi_dvd_of_dvd_p_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:15:51.428176+00:00
-- url     : https://prove2.me/submissions/b51ec62a-a76c-468f-9226-ca533f0c8090

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_xi
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_eq_zero_iff
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
variable [ValuationRing R]
variable [CharZero R]
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution (ϖ : PFlat p R) {x : Ainf p R} {k : ℕ}
    (h : xi ϖ ∣ (p : Ainf p R) ^ k * x) : xi ϖ ∣ x := by
  rw [← theta_eq_zero_iff] at h ⊢
  simpa [(Fact.out : p.Prime).ne_zero] using h
end Reformulated.AutPerF.Ainf
