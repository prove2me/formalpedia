-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.theta_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:32:59.187993+00:00
-- url     : https://prove2.me/submissions/9fb93482-d54c-4382-aa32-ac9f2b69d38f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Theorems.Thm_Reformulated_AutPerF_Tilt_untilt_map

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
variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution (f : R →+* S) (x : Ainf p R) : theta p S (map p f x) = f (theta p R x) := by
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : S)})]
  intro n
  rw [smul_eq_mul, Ideal.mul_top, SModEq]
  have := WittVector.eq_of_apply_teichmuller_eq
    ((Ideal.Quotient.mk (span {(p : S)} ^ n)).comp ((theta p S).comp (map p f)))
    ((Ideal.Quotient.mk (span {(p : S)} ^ n)).comp (f.comp (theta p R)))
    (by
      refine ⟨n, ?_⟩
      rw [← map_natCast (Ideal.Quotient.mk (span {(p : S)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (mem_span_singleton_self _) _)
    (by intro y; simp [Tilt.untilt_map])
  exact RingHom.congr_fun this x
end Reformulated.AutPerF.Ainf
