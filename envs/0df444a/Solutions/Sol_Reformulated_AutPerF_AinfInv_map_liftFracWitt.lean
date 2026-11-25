-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.map_liftFracWitt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:22:11.324868+00:00
-- url     : https://prove2.me/submissions/a6cc6a05-64c1-44f3-a55a-cc49a8c109bc

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Theorems.Thm_Reformulated_AutPerF_Ainf_ofWitt_teichmuller
import Theorems.Thm_Reformulated_AutPerF_Ainf_map_liftWitt
import Theorems.Thm_Reformulated_AutPerF_fracWittLift_algebraMap
import Theorems.Thm_Reformulated_AutPerF_fracWitt_hom_ext
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
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]
variable {p}
namespace Reformulated.AutPerF
namespace AinfInv
theorem _root_.solution (e : R →+* S) (g : WittVector p k →+* R)
    (x : FractionRing (WittVector p k)) :
    AinfInv.map p e (AinfInv.liftFracWitt p g x) = AinfInv.liftFracWitt p (e.comp g) x :=
  RingHom.congr_fun (fracWitt_hom_ext (f := (AinfInv.map p e).comp (AinfInv.liftFracWitt p g))
    (g := AinfInv.liftFracWitt p (e.comp g)) (by simp [Ainf.map_liftWitt])) x
end AinfInv
end Reformulated.AutPerF
