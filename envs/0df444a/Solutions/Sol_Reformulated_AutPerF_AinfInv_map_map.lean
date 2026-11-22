-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.map_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:57:38.769361+00:00
-- url     : https://prove2.me/submissions/060aa880-fdab-4336-acf3-1d47a973c255

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Theorems.Thm_Reformulated_AutPerF_Tilt_map_map
import Theorems.Thm_Reformulated_AutPerF_Ainf_map_map

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
open Reformulated.AutPerF.AinfInv
variable {p}
namespace Reformulated.AutPerF.AinfInv
theorem _root_.solution (f : R →+* S) (g : S →+* U) (x : AinfInv p R) :
    map p g (map p f x) = map p (g.comp f) x :=
  RingHom.congr_fun (hom_ext (f := (map p g).comp (map p f)) (g := map p (g.comp f))
    (by simp [Ainf.map_map])) x
end Reformulated.AutPerF.AinfInv
