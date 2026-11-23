-- Prove2me | solution 1 for Reformulated.AutPerF.BdR.map_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:25.933524+00:00
-- url     : https://prove2.me/submissions/d39055da-02c9-4d8e-b6c8-34c534ee4d27

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_mapEquiv_apply
import Theorems.Thm_Reformulated_AutPerF_BdR_hom_ext
import Theorems.Thm_Reformulated_AutPerF_BdR_map_algebraMap
import Theorems.Thm_Reformulated_AutPerF_BdR_map_algebraMap_padic
import Theorems.Thm_Reformulated_AutPerF_BdR_map_refl
import Theorems.Thm_Reformulated_AutPerF_AinfInv_map_map
import Theorems.Thm_Reformulated_AutPerF_Ainf_map_map
import Theorems.Thm_Reformulated_AutPerF_Bst_hom_ext
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


attribute [local simp] Reformulated.AutPerF.BdRPlus.mapEquiv_apply
attribute [local simp] Reformulated.AutPerF.BdR.map_algebraMap
attribute [local simp] Reformulated.AutPerF.BdR.map_algebraMap_padic
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
theorem _root_.solution (e : R ≃+* S) (e' : S ≃+* U) (x : BdR p R) :
    map p e' (map p e x) = map p (e.trans e') x :=
  RingHom.congr_fun (hom_ext (f := (map p e').toRingHom.comp (map p e).toRingHom)
    (g := (map p (e.trans e')).toRingHom) (by simp [BdRPlus.map_map])) x
end Reformulated.AutPerF.BdR
