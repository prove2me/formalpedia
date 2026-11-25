-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_ringHom_of_root_e8ffa89b6ad9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:55:15.62799+00:00
-- url     : https://prove2.me/submissions/947252b2-4925-4455-8149-2dd5e94db9b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConstantsDescend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConstantsDescend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_aeval_mk_map_8e48c39d9389

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
theorem _root_.solution (θ : B) (hgen : Algebra.adjoin A {θ} = ⊤) (I : Ideal A) [I.IsMaximal]
    (σ : A ⧸ I →+* ℂ) (β : ℂ)
    (hβ : ((minpoly (A ⧸ I) (Ideal.Quotient.mk (I.map (algebraMap A B)) θ)).map σ).IsRoot β) :
    ∃ w : B →+* ℂ, w.comp (algebraMap A B) = σ.comp (Ideal.Quotient.mk I) ∧ w θ = β := by
  classical
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  let f : A[X] →+* B := (aeval θ).toRingHom
  have hf : Function.Surjective f := by
    intro b
    have hb : b ∈ Algebra.adjoin A {θ} := hgen ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
    obtain ⟨P, rfl⟩ := hb
    exact ⟨P, rfl⟩
  let g : A[X] →+* ℂ := eval₂RingHom (σ.comp (Ideal.Quotient.mk I)) β
  have hg : ∀ P : A[X], g P = ((P.map (algebraMap A (A ⧸ I))).map σ).eval β := by
    intro P
    rw [eval_map, eval₂_map, Ideal.Quotient.algebraMap_eq]
    rfl
  have hker : RingHom.ker f ≤ RingHom.ker g := by
    intro P hP
    rw [RingHom.mem_ker] at hP ⊢
    have h1 : aeval (Ideal.Quotient.mk (I.map (algebraMap A B)) θ) (P.map (algebraMap A (A ⧸ I))) = 0 := by
      rw [aeval_mk_map]
      change Ideal.Quotient.mk _ (f P) = 0
      rw [hP, map_zero]
    obtain ⟨r, hr⟩ := minpoly.dvd _ _ h1
    rw [hg, hr, Polynomial.map_mul, eval_mul, hβ.eq_zero, zero_mul]
  obtain ⟨w, hw⟩ : ∃ w : B →+* ℂ, ∀ P, w (f P) = g P := by
    refine ⟨(Ideal.Quotient.lift (RingHom.ker f) g hker).comp
      (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom, fun P => ?_⟩
    have he : (RingHom.quotientKerEquivOfSurjective hf).symm (f P) = Ideal.Quotient.mk (RingHom.ker f) P := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, he]
    exact Ideal.Quotient.lift_mk _ _ _
  refine ⟨w, ?_, ?_⟩
  · ext a
    have := hw (C a)
    simp only [f, g, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, coe_eval₂RingHom, eval₂_C] at this
    simpa using this
  · have := hw X
    simpa [f, g] using this
end GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
