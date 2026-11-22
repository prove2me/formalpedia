-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.frob_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:07.307804+00:00
-- url     : https://prove2.me/submissions/834addb2-b024-46ac-91dd-0a98c7be66e9

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
open Reformulated.AutPerF.Ainf
variable {p}
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution : Function.Bijective (frob p R) := WittVector.frobenius_bijective p _
end Reformulated.AutPerF.Ainf
