-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointIntegral_isFiniteProjection_f9667751e3c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:25.968049+00:00
-- url     : https://prove2.me/submissions/1762cb94-4608-4872-9cd7-33bd4ef38f9a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPointIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.PointIntegral
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.PointIntegral
theorem _root_.solution (p : Fin n → ℂ) (A : Matrix (Fin 0) (Fin n) ℂ) :
    IsFiniteProjection (RingHom.ker (MvPolynomial.eval p)) A := by
  have hsurj : Function.Surjective (projHom (RingHom.ker (MvPolynomial.eval p)) A) := by
    intro q
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨C (eval p q), ?_⟩
    simp only [projHom, pullback, AlgHom.comp_apply, aeval_C, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq, RingHom.mem_ker]
    simp
  refine ⟨?_, ?_⟩
  · intro P Q hPQ
    obtain ⟨a, rfl⟩ : ∃ a, P = C a := ⟨coeff 0 P, (eq_C_of_isEmpty P)⟩
    obtain ⟨b, rfl⟩ : ∃ b, Q = C b := ⟨coeff 0 Q, (eq_C_of_isEmpty Q)⟩
    simp only [projHom, pullback, AlgHom.comp_apply, aeval_C, Ideal.Quotient.mkₐ_eq_mk] at hPQ
    rw [Ideal.Quotient.eq, RingHom.mem_ker] at hPQ
    simp [sub_eq_zero] at hPQ
    rw [hPQ]
  · exact RingHom.Finite.of_surjective _ hsurj
end GroundTheory.Heights₂.Heights.PointIntegral
