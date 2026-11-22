-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.map_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:54:32.686524+00:00
-- url     : https://prove2.me/submissions/ca784b0f-e4fa-43c3-89e5-9fd10720194c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Theorems.Thm_Reformulated_AutPerF_Tilt_map_map

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
theorem _root_.solution (f : R →+* S) (g : S →+* U) (x : Ainf p R) :
    map p g (map p f x) = map p (g.comp f) x := by
  ext n; simp [map, Tilt.map_map]
end Reformulated.AutPerF.Ainf
