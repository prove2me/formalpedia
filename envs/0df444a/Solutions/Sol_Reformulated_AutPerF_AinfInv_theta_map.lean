-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.theta_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:38:29.962537+00:00
-- url     : https://prove2.me/submissions/3e7fd29f-d728-434e-ba77-af7cb328fa73

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_map
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap

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
variable {p}
namespace Reformulated.AutPerF
namespace AinfInv
theorem _root_.solution [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]
    (f : R →+* S) (x : AinfInv p R) :
    AinfInv.theta p S (AinfInv.map p f x) = awayMap p f (AinfInv.theta p R x) :=
  RingHom.congr_fun (AinfInv.hom_ext (f := (AinfInv.theta p S).comp (AinfInv.map p f))
    (g := (awayMap p f).comp (AinfInv.theta p R)) (by simp [Ainf.theta_map])) x
end AinfInv
end Reformulated.AutPerF
