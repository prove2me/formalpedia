-- Prove2me | solution 1 for Reformulated.AutPerF.Tilt.map_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:00.733418+00:00
-- url     : https://prove2.me/submissions/2a928720-4eb5-4746-beb1-fbaff063a990

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
open Reformulated.AutPerF.Tilt
variable {p}
namespace Reformulated.AutPerF.Tilt
theorem _root_.solution (f : R →+* S) (g : S →+* U) (x : Tilt p R) :
    map p g (map p f x) = map p (g.comp f) x := by
  refine ext fun n => ?_
  rw [coeff_map, coeff_map, coeff_map]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  rw [← ha]; rfl
end Reformulated.AutPerF.Tilt
