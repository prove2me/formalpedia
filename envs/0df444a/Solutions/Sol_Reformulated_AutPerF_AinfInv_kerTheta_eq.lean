-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.kerTheta_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:54.147053+00:00
-- url     : https://prove2.me/submissions/743211f2-9d16-4e58-b408-c331805a8593

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_xi
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_eq_zero_iff
import Theorems.Thm_Reformulated_AutPerF_AinfInv_exists_p_pow_mul_eq
import Theorems.Thm_Reformulated_AutPerF_AinfInv_algebraMap_away_injective
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
open Reformulated.AutPerF.AinfInv
variable [IsDomain R]
variable [ValuationRing R]
variable [CharZero R]
namespace Reformulated.AutPerF.AinfInv
theorem _root_.solution (ϖ : PFlat p R) :
    kerTheta p R = span {algebraMap (Ainf p R) (AinfInv p R) (Ainf.xi ϖ)} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨k, a, h⟩ := exists_p_pow_mul_eq x
    have h1 : theta p R (algebraMap _ _ a) = 0 := by
      rw [← h, map_mul, show theta p R x = 0 from hx, mul_zero]
    rw [theta_algebraMap, map_eq_zero_iff _ algebraMap_away_injective,
      Ainf.theta_eq_zero_iff ϖ] at h1
    rw [mem_span_singleton, ← ((isUnit_p (R := R) p).pow k).dvd_mul_left, h]
    exact map_dvd _ h1
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    simp [RingHom.mem_ker]
end Reformulated.AutPerF.AinfInv
