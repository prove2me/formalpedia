-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.map_frob
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:03.522814+00:00
-- url     : https://prove2.me/submissions/fd255b12-efe2-4176-ab18-d0abbfb42f0b

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
theorem _root_.solution (f : R →+* S) (x : Ainf p R) : map p f (frob p R x) = frob p S (map p f x) := by
  ext n; simp [map, frob_eq_map, frobenius_def]
end Reformulated.AutPerF.Ainf
