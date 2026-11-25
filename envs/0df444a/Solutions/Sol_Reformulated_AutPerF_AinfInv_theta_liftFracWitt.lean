-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.theta_liftFracWitt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:22:16.054052+00:00
-- url     : https://prove2.me/submissions/631840cb-a017-4328-a489-7a03469e53d9

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Theorems.Thm_Reformulated_AutPerF_Ainf_ofWitt_teichmuller
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_liftWitt
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
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]
variable {p}
namespace Reformulated.AutPerF
namespace AinfInv
theorem _root_.solution [IsAdicComplete (span {(p : R)}) R] (g : WittVector p k →+* R)
    (a : WittVector p k) :
    AinfInv.theta p R (AinfInv.liftFracWitt p g (algebraMap _ _ a)) = algebraMap R _ (g a) := by
  simp [Ainf.theta_liftWitt]
end AinfInv
end Reformulated.AutPerF
