-- Prove2me | solution 1 for Reformulated.AutPerF.Bcris.map_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:33.099654+00:00
-- url     : https://prove2.me/submissions/9bec81e5-0acf-46c3-9e2d-486294f0a164

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
import Theorems.Thm_Reformulated_AutPerF_AcrisZero_map_frob
import Theorems.Thm_Reformulated_AutPerF_Acris_map_frob
import Theorems.Thm_Reformulated_AutPerF_BcrisPlus_map_frob
import Theorems.Thm_Reformulated_AutPerF_Acris_hom_ext
import Theorems.Thm_Reformulated_AutPerF_AinfInv_map_frob
import Theorems.Thm_Reformulated_AutPerF_Ainf_map_frob
import Theorems.Thm_Reformulated_AutPerF_Bcris_logTeich_one
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
theorem _root_.solution (f : R →+* S) (hf : Function.Injective f) (x : Bcris p R) :
    map p f hf (frob p R x) = frob p S (map p f hf x) :=
  RingHom.congr_fun (hom_ext (f := (map p f hf).comp (frob p R))
    (g := (frob p S).comp (map p f hf)) (by simp [BcrisPlus.map_frob])) x
end Reformulated.AutPerF.Bcris
