-- Prove2me | solution 1 for Reformulated.AutPerF.tateModule.map_padicPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:32:28.798576+00:00
-- url     : https://prove2.me/submissions/bb7b6626-b0b8-4fb0-a700-7089d468a81e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_MapEqPadicPowCyclotomicCharacter
import Theorems.Thm_Reformulated_AutPerF_Tilt_seq_map

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
theorem _root_.solution (f : R →+* S) (η : tateModule p R) (η' : tateModule p S)
    (h : Tilt.map p f η.1 = η'.1) (a : ℤ_[p]) :
    Tilt.map p f (padicPow η a).1 = (padicPow η' a).1 :=
  Tilt.ext_seq fun n => by rw [seq_map, seq_padicPow, seq_padicPow, map_pow, ← seq_map, h]
end Reformulated.AutPerF.tateModule
