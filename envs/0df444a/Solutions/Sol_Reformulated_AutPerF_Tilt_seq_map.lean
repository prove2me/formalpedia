-- Prove2me | solution 1 for Reformulated.AutPerF.Tilt.seq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:49:59.688887+00:00
-- url     : https://prove2.me/submissions/54ce860f-0b27-42d0-a2ea-a459e0b40a6e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_MapEqPadicPowCyclotomicCharacter
import Theorems.Thm_Reformulated_AutPerF_Tilt_mk_seq

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
open Reformulated.AutPerF.Tilt
namespace Reformulated.AutPerF.Tilt
theorem _root_.solution (f : R →+* S) (y : Tilt p R) (n : ℕ) : seq n (map p f y) = f (seq n y) := by
  have : map p f y = ofSeq (fun n => f (seq n y)) (fun n => by rw [← map_pow, seq_succ_pow]) := by
    refine ext fun n => ?_
    rw [coeff_map, ← mk_seq, ← mk_seq, seq_ofSeq]
    rfl
  rw [this, seq_ofSeq]
end Reformulated.AutPerF.Tilt
