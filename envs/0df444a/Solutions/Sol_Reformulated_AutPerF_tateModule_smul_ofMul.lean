-- Prove2me | solution 1 for Reformulated.AutPerF.tateModule.smul_ofMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:32:35.432968+00:00
-- url     : https://prove2.me/submissions/36fc5dc4-8f71-4c01-afb7-ce66635d2707

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_MapEqPadicPowCyclotomicCharacter

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
open Reformulated.AutPerF.tateModule
open Tilt
namespace Reformulated.AutPerF.tateModule
theorem _root_.solution (a : ℤ_[p]) (η : tateModule p R) :
    a • Additive.ofMul η = Additive.ofMul (padicPow η a) := rfl
end Reformulated.AutPerF.tateModule
