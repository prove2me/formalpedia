-- Prove2me | solution 1 for Reformulated.AutPerF.Acris.map_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:59:44.300826+00:00
-- url     : https://prove2.me/submissions/f42cb33f-c487-445f-9ba3-d9f09bc3e301

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
import Theorems.Thm_Reformulated_AutPerF_AcrisZero_map_frob
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
open Reformulated.AutPerF.Acris
namespace Reformulated.AutPerF.Acris
theorem _root_.solution (f : R →+* S) (x : Acris p R) : map p f (frob p R x) = frob p S (map p f x) :=
  RingHom.congr_fun (hom_ext (f := (map p f).comp (frob p R)) (g := (frob p S).comp (map p f))
    (by simp [AcrisZero.map_frob])) x
end Reformulated.AutPerF.Acris
