-- Prove2me | solution 1 for Reformulated.AutPerF.awayMap_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:45.673601+00:00
-- url     : https://prove2.me/submissions/545aed22-3139-42ec-81ec-c6dfa61793af

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap

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
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)]
variable (S : Type v) [CommRing S] [Fact ¬IsUnit (p : S)]
variable (U : Type w) [CommRing U] [Fact ¬IsUnit (p : U)]
variable {R S U}
omit [Fact p.Prime]
namespace Reformulated.AutPerF
theorem _root_.solution {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : R) : awayMap p f (algebraMap _ _ x) = algebraMap _ _ (f x) :=
  IsLocalization.Away.lift_eq _ _ x
end Reformulated.AutPerF
