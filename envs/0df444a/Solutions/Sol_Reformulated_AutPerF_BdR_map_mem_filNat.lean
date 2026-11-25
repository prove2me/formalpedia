-- Prove2me | solution 1 for Reformulated.AutPerF.BdR.map_mem_filNat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:50:39.186078+00:00
-- url     : https://prove2.me/submissions/39169115-8d53-47ea-a7fa-8c5a396878b5

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_map_mem_fil
import Theorems.Thm_Reformulated_AutPerF_BdR_map_algebraMap
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


attribute [local simp] Reformulated.AutPerF.BdR.map_algebraMap

set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]
open Reformulated.AutPerF.BdR
variable {p}
namespace Reformulated.AutPerF.BdR
theorem _root_.solution (e : R ≃+* S) {n : ℕ} {x : BdR p R} (hx : x ∈ filNat p R n) :
    map p e x ∈ filNat p S n := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨_, BdRPlus.map_mem_fil (e : R →+* S) hy, (map_algebraMap e y).symm⟩
end Reformulated.AutPerF.BdR
