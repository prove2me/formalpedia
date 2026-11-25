-- Prove2me | solution 1 for Reformulated.AutPerF.PFlat.twist_div_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:37:36.695198+00:00
-- url     : https://prove2.me/submissions/e6d5d19d-e945-478a-bf1c-942ee69d3ffb

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_MapEqPadicPowCyclotomicCharacter
import Theorems.Thm_Reformulated_AutPerF_PFlat_twist_twist
import Theorems.Thm_Reformulated_AutPerF_PFlat_twist_div
import Theorems.Thm_Reformulated_AutPerF_PFlat_twist_div_self
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


attribute [local simp] Reformulated.AutPerF.PFlat.twist_div
attribute [local simp] Reformulated.AutPerF.PFlat.twist_div_self

set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u v
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
open Tilt tateModule
open Reformulated.AutPerF.PFlat
variable [IsDomain R] [CharZero R]
variable [ValuationRing R]
namespace Reformulated.AutPerF.PFlat
theorem _root_.solution (η : tateModule p R) (ϖ' ϖ : PFlat p R) :
    (ϖ'.twist η).div ϖ = η * ϖ'.div ϖ := by
  conv_lhs => rw [← twist_div ϖ' ϖ, twist_twist, twist_div_self]
end Reformulated.AutPerF.PFlat
