-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.theta_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:53:06.808921+00:00
-- url     : https://prove2.me/submissions/0b8d8212-cc32-4fc4-bdfd-9fca0aac5fa6

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_xi
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_surjective
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
namespace Reformulated.AutPerF.AinfInv
theorem _root_.solution [IsAlgClosed (FractionRing R)] : Function.Surjective (theta p R) := by
  intro y
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (p : R) y
  obtain ⟨b, rfl⟩ := Ainf.theta_surjective (p := p) a
  obtain ⟨u, hu⟩ := isUnit_p (R := R) p
  refine ⟨algebraMap _ _ b * ↑(u⁻¹ ^ k), ?_⟩
  rw [map_mul, theta_algebraMap, ← h, map_natCast, mul_assoc, ← map_natCast (theta p R), ← map_pow,
    ← map_mul, ← hu]
  simp [← mul_pow]
end Reformulated.AutPerF.AinfInv
