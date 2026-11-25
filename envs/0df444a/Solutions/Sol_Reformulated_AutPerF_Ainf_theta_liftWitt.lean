-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.theta_liftWitt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:11:52.482544+00:00
-- url     : https://prove2.me/submissions/04c3508d-426c-4c8e-bd5b-a9ecd907de5c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Theorems.Thm_Reformulated_AutPerF_Ainf_ofWitt_teichmuller
import Theorems.Thm_Reformulated_AutPerF_wittResidueMap_coeff_zero
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap


attribute [local simp] Reformulated.AutPerF.Ainf.ofWitt_teichmuller

set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
variable {k : Type w} [CommRing k] [CharP k p] [PerfectRing k p]
variable {p}
namespace Reformulated.AutPerF
namespace Ainf
theorem _root_.solution [IsAdicComplete (span {(p : R)}) R] (g : WittVector p k →+* R)
    (x : WittVector p k) : Ainf.theta p R (Ainf.liftWitt p g x) = g x := by
  have key (a : k) : PreTilt.untilt (Tilt.ofPerfect p (wittResidueMap p g) a) =
      g (WittVector.teichmuller p a) := by
    refine Perfection.teichmuller_spec fun n => ?_
    refine ⟨g (WittVector.teichmuller p ((frobeniusEquiv k p).symm^[n] a)), ?_, ?_⟩
    · rw [← wittResidueMap_coeff_zero, WittVector.teichmuller_coeff_zero]
      rfl
    · rw [← map_pow, ← map_pow, ← iterate_frobenius,
        Function.RightInverse.iterate (frobenius_apply_frobeniusEquiv_symm k p) n]
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : R)})]
  intro n
  rw [smul_eq_mul, Ideal.mul_top, SModEq]
  have := WittVector.eq_of_apply_teichmuller_eq
    ((Ideal.Quotient.mk (span {(p : R)} ^ n)).comp ((Ainf.theta p R).comp (Ainf.liftWitt p g)))
    ((Ideal.Quotient.mk (span {(p : R)} ^ n)).comp g)
    (by
      refine ⟨n, ?_⟩
      rw [← map_natCast (Ideal.Quotient.mk (span {(p : R)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (mem_span_singleton_self _) _)
    (by intro y; simp [Ainf.liftWitt, key])
  exact RingHom.congr_fun this x
end Ainf
end Reformulated.AutPerF
