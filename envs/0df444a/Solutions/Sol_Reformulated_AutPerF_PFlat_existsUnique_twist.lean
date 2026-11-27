-- Prove2me | solution 1 for Reformulated.AutPerF.PFlat.existsUnique_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:22.574015+00:00
-- url     : https://prove2.me/submissions/13781551-b187-4e62-995b-83b094394d1c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_MapEqPadicPowCyclotomicCharacter
import Theorems.Thm_Reformulated_AutPerF_PFlat_twist_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (ϖ ϖ' : PFlat p R) : ∃! η : tateModule p R, ϖ' = ϖ.twist η := by
  obtain ⟨η, hη⟩ := twist_surjective ϖ ϖ'
  exact ⟨η, hη.symm, fun η' h => twist_injective ϖ (h.symm.trans hη.symm)⟩
end Reformulated.AutPerF.PFlat
