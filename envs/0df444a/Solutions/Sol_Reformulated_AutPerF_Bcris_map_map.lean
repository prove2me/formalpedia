-- Prove2me | solution 1 for Reformulated.AutPerF.Bcris.map_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:26:36.4112+00:00
-- url     : https://prove2.me/submissions/1239b7a2-7f33-43f2-8fc0-806880c493ba

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
import Theorems.Thm_Reformulated_AutPerF_tateModule_map_map
import Theorems.Thm_Reformulated_AutPerF_PFlat_map_map
import Theorems.Thm_Reformulated_AutPerF_AcrisZero_map_map
import Theorems.Thm_Reformulated_AutPerF_Acris_map_map
import Theorems.Thm_Reformulated_AutPerF_BcrisPlus_map_map
import Theorems.Thm_Reformulated_AutPerF_Acris_hom_ext
import Theorems.Thm_Reformulated_AutPerF_AinfInv_map_map
import Theorems.Thm_Reformulated_AutPerF_Ainf_map_map
import Theorems.Thm_Reformulated_AutPerF_Bcris_logTeich_one
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
attribute [local simp] Reformulated.AutPerF.Bcris.logTeich_one
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap



set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]
variable {p}
open Reformulated.AutPerF.Bcris
namespace Reformulated.AutPerF.Bcris
theorem _root_.solution (f : R →+* S) (hf : Function.Injective f) (g : S →+* U)
    (hg : Function.Injective g) (hgf : Function.Injective (g.comp f)) (x : Bcris p R) :
    map p g hg (map p f hf x) = map p (g.comp f) hgf x :=
  RingHom.congr_fun (hom_ext (f := (map p g hg).comp (map p f hf)) (g := map p (g.comp f) hgf)
    (by simp [BcrisPlus.map_map])) x
end Reformulated.AutPerF.Bcris
