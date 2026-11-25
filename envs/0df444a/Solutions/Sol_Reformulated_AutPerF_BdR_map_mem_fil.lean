-- Prove2me | solution 1 for Reformulated.AutPerF.BdR.map_mem_fil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:01:54.154102+00:00
-- url     : https://prove2.me/submissions/7050c949-bc33-483d-8c0a-a99a23842c97

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap
import Theorems.Thm_Reformulated_AutPerF_BdR_map_refl
import Theorems.Thm_Reformulated_AutPerF_BdR_map_map
import Theorems.Thm_Reformulated_AutPerF_BdR_map_mem_filNat
import Theorems.Thm_Reformulated_AutPerF_AinfInv_map_map
import Theorems.Thm_Reformulated_AutPerF_Ainf_map_map
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_Tilt_map_map
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


attribute [local simp] Reformulated.AutPerF.BdR.map_refl

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
theorem _root_.solution (e : R ≃+* S) {i : ℤ} {x : BdR p R} (hx : x ∈ fil p R i) :
    map p e x ∈ fil p S i := by
  rw [fil, Submodule.mem_div_iff_forall_mul_mem] at hx ⊢
  intro y hy
  have h := map_mem_filNat e (hx _ (map_mem_filNat e.symm hy))
  rwa [map_mul, map_map, RingEquiv.symm_trans_self, map_refl] at h
end Reformulated.AutPerF.BdR
