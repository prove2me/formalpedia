-- Prove2me | solution 1 for Reformulated.AutPerF.BdR.map_refl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:10.035797+00:00
-- url     : https://prove2.me/submissions/847e6a64-ca93-42a2-8696-ff43aa88891f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_mapEquiv_apply
import Theorems.Thm_Reformulated_AutPerF_BdR_hom_ext
import Theorems.Thm_Reformulated_AutPerF_BdR_map_algebraMap
import Theorems.Thm_Reformulated_AutPerF_BdR_map_algebraMap_padic
import Theorems.Thm_Reformulated_AutPerF_Bst_hom_ext
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


attribute [local simp] Reformulated.AutPerF.BdRPlus.mapEquiv_apply
attribute [local simp] Reformulated.AutPerF.BdR.map_algebraMap
attribute [local simp] Reformulated.AutPerF.BdR.map_algebraMap_padic

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
theorem _root_.solution (x : BdR p R) : map p (RingEquiv.refl R) x = x :=
  RingHom.congr_fun (hom_ext (f := (map p (RingEquiv.refl R) : _ →+* _)) (g := RingHom.id _)
    (by simp)) x
end Reformulated.AutPerF.BdR
