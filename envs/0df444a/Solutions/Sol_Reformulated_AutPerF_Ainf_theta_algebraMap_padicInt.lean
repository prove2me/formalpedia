-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.theta_algebraMap_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:20:39.654841+00:00
-- url     : https://prove2.me/submissions/e92e5730-edb8-42c4-a9c4-852676849449

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Theorems.Thm_Reformulated_AutPerF_Ainf_ofWitt_teichmuller
import Theorems.Thm_Reformulated_AutPerF_fracWittLift_algebraMap
import Theorems.Thm_Reformulated_AutPerF_AinfInv_liftFracWitt_algebraMap
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


attribute [local simp] Reformulated.AutPerF.Ainf.ofWitt_teichmuller
attribute [local simp] Reformulated.AutPerF.fracWittLift_algebraMap
attribute [local simp] Reformulated.AutPerF.AinfInv.liftFracWitt_algebraMap

set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
variable [IsAdicComplete (span {(p : R)}) R]
variable {p}
namespace Reformulated.AutPerF
namespace Ainf
theorem _root_.solution (g : ℤ_[p] →+* R) (a : ℤ_[p]) :
    Ainf.theta p R (algebraMap ℤ_[p] _ a) = g a := by
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : R)})]
  intro n
  rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n a)
  have ha : a = (PadicInt.appr a n : ℤ_[p]) + c * (p : ℤ_[p]) ^ n := by rw [hc]; ring
  rw [ha, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  simp only [map_add, map_mul, map_pow, map_natCast]
  exact ⟨Ainf.theta p R (algebraMap ℤ_[p] _ c) - g c, by ring⟩
end Ainf
end Reformulated.AutPerF
