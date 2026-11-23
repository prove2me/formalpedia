-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.theta_surjective_of_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:48.253866+00:00
-- url     : https://prove2.me/submissions/71feceb2-72d5-4dba-a9fe-b690d8bac943

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
namespace Reformulated.AutPerF
namespace AinfInv
theorem _root_.solution
    (hF : Function.Surjective (frobenius (ModP R p) p)) :
    Function.Surjective (AinfInv.theta p R) := by
  intro y
  obtain ⟨⟨a, _, n, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers (p : R)) y
  obtain ⟨b, rfl⟩ := surjective_fontaineTheta hF a
  obtain ⟨u, hu⟩ := (AinfInv.isUnit_p p (R := R)).pow n
  refine ⟨algebraMap _ _ b * ↑u⁻¹, ?_⟩
  simp only [map_pow, map_natCast] at h
  have h2 : AinfInv.theta p R ↑u = (p : Localization.Away (p : R)) ^ n := by
    rw [hu, map_pow, map_natCast]
  rw [map_mul, AinfInv.theta_algebraMap, Ainf.theta, ← h, ← h2, mul_assoc, ← map_mul,
    Units.mul_inv, map_one, mul_one]
end AinfInv
end Reformulated.AutPerF
