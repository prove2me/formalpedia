-- Prove2me | solution 1 for Reformulated.AutPerF.Tilt.untilt_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:27:52.78192+00:00
-- url     : https://prove2.me/submissions/33bf982e-be68-4510-99e4-a76b51e9acdd

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
variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]
namespace Reformulated.AutPerF.Tilt
theorem _root_.solution (f : R →+* S) (x : Tilt p R) :
    PreTilt.untilt (map p f x) = f (PreTilt.untilt x) := by
  refine Perfection.teichmuller_spec fun n => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  refine ⟨f a, ?_, ?_⟩
  · change _ = PreTilt.coeff n (map p f x)
    rw [coeff_map, ← ha]; rfl
  · have h := Perfection.teichmuller_sModEq (p := p) (I := span {(p : R)}) (x := x) (y := a)
      (n := n) ha
    rw [SModEq.sub_mem] at h ⊢
    have h2 := pow_le_comap_pow (span_natCast_le_comap p f) (n + 1) (neg_mem h)
    rw [Ideal.mem_comap, neg_sub, map_sub, map_pow] at h2
    exact h2
end Reformulated.AutPerF.Tilt
