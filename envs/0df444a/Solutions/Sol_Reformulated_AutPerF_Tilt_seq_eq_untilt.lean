-- Prove2me | solution 1 for Reformulated.AutPerF.Tilt.seq_eq_untilt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:37.292368+00:00
-- url     : https://prove2.me/submissions/aab30f01-c619-4c31-8929-ac14900a3db7

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
open Reformulated.AutPerF.Tilt
namespace Reformulated.AutPerF.Tilt
theorem _root_.solution (y : Tilt p R) (n : ℕ) :
    seq n y = PreTilt.untilt (((frobeniusEquiv (Tilt p R) p).symm)^[n] y) := by
  induction n generalizing y with
  | zero => exact seq_zero y
  | succ n ih => rw [Function.iterate_succ_apply, ← ih, seq_frobeniusEquiv_symm]
end Reformulated.AutPerF.Tilt
