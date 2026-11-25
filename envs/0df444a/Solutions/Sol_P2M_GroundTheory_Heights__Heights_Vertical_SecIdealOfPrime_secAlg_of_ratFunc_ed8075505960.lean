-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecIdealOfPrime_secAlg_of_ratFunc_ed8075505960
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:24.759314+00:00
-- url     : https://prove2.me/submissions/780aa03c-e26c-4b99-b1b6-faec1699a5fe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecIdealOfPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenSecKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecIdealOfPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecIdealOfPrime
namespace GroundTheory.Heights₂.Heights.Vertical.SecIdealOfPrime
theorem _root_.solution {k E : Type} [Field k] [Field E] (n e : ℕ) (φ : k →+* E) (y : Par e n → E)
    (hinj : Function.Injective (eval₂Hom φ y))
    (hsurj : ∀ z : E, ∃ a b, z = eval₂Hom φ y a / eval₂Hom φ y b)
    (Q : Ideal (MvPolynomial (Fin n) k)) (hQF : IsField (GenSec k e Q))
    (hQK : RingHom.ker ((Ideal.Quotient.mk
        (secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n))).comp
          (MvPolynomial.map (algebraMap k (GenParField k e n)))) = Q) :
    IsField (SecAlg (Q.map (MvPolynomial.map φ)) y) ∧
      RingHom.ker ((Ideal.Quotient.mk (secIdeal (Q.map (MvPolynomial.map φ)) y)).comp
        (MvPolynomial.map φ)) = Q := by
  let _ : Algebra (MvPolynomial (Par e n) k) E := (eval₂Hom φ y).toAlgebra
  have : FaithfulSMul (MvPolynomial (Par e n) k) E :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : IsFractionRing (MvPolynomial (Par e n) k) E := IsFractionRing.of_field _ _ hsurj
  let σ : GenParField k e n ≃ₐ[MvPolynomial (Par e n) k] E := FractionRing.algEquiv _ E
  have hσX : ∀ p, σ (genPar k e n p) = y p := fun p => by
    show σ (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n) (X p)) = y p
    exact (σ.commutes (X p)).trans (eval₂_X _ _ p)
  have hσC : (σ : GenParField k e n →+* E).comp (algebraMap k (GenParField k e n)) = φ := by
    refine RingHom.ext fun c => ?_
    show σ (algebraMap k (GenParField k e n) c) = φ c
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Par e n) k) (GenParField k e n), σ.commutes]
    exact eval₂_C _ _ _
  have hmm : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ₁ : A →+* B) (φ₂ : B →+* C),
      (MvPolynomial.map φ₂).comp (MvPolynomial.map φ₁) =
        (MvPolynomial.map (φ₂.comp φ₁) : MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) C) :=
    fun φ₁ φ₂ ↦ RingHom.ext fun p ↦ MvPolynomial.map_map _ _ p
  let QF := Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))
  let QE := Q.map (MvPolynomial.map φ)
  let M : MvPolynomial (Fin n) (GenParField k e n) ≃+* MvPolynomial (Fin n) E :=
    MvPolynomial.mapEquiv (Fin n) σ.toRingEquiv
  have hmσ : (M : MvPolynomial (Fin n) (GenParField k e n) →+* MvPolynomial (Fin n) E) =
      MvPolynomial.map (σ : GenParField k e n →+* E) :=
    RingHom.ext fun _ => rfl
  have hIJ : secIdeal QE y = (secIdeal QF (genPar k e n)).map
      (M : MvPolynomial (Fin n) (GenParField k e n) →+* MvPolynomial (Fin n) E) := by
    rw [hmσ]
    simp only [secIdeal, Ideal.map_sup, Ideal.map_span, QF, QE, Ideal.map_map, hmm, hσC]
    congr 3
    · rw [← Set.range_comp]
      congr 1
      funext i
      simp [secForm, linForm, hσX]
    · rw [Set.image_singleton]
      congr 1
      simp [chartForm, linForm, hσX]
  let τ : GenSec k e Q ≃+* SecAlg QE y := Ideal.quotientEquiv _ _ M hIJ
  refine ⟨MulEquiv.isField hQF τ.symm.toMulEquiv, ?_⟩
  have hc : (Ideal.Quotient.mk (secIdeal QE y)).comp (MvPolynomial.map φ) =
      (τ : GenSec k e Q →+* SecAlg QE y).comp
        ((Ideal.Quotient.mk (secIdeal QF (genPar k e n))).comp
          (MvPolynomial.map (algebraMap k (GenParField k e n)))) := by
    refine RingHom.ext fun p => ?_
    show Ideal.Quotient.mk (secIdeal QE y) (MvPolynomial.map φ p) =
      Ideal.Quotient.mk (secIdeal QE y) (MvPolynomial.map (σ : GenParField k e n →+* E)
        (MvPolynomial.map (algebraMap k (GenParField k e n)) p))
    rw [MvPolynomial.map_map, hσC]
  rw [hc, RingHom.ker_comp_of_injective _ (f := (τ : GenSec k e Q →+* SecAlg QE y)) τ.injective]
  exact hQK
end GroundTheory.Heights₂.Heights.Vertical.SecIdealOfPrime
