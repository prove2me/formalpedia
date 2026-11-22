-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.map_frob
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:54:34.344087+00:00
-- url     : https://prove2.me/submissions/8581063a-332b-4aa9-b1f2-99568c6f36bd

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Theorems.Thm_Reformulated_AutPerF_Ainf_map_frob

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
theorem _root_.solution (f : R →+* S) (x : AinfInv p R) : map p f (frob p R x) = frob p S (map p f x) :=
  RingHom.congr_fun (hom_ext (f := (map p f).comp (frob p R)) (g := (frob p S).comp (map p f))
    (by simp [Ainf.map_frob])) x
end Reformulated.AutPerF.AinfInv
