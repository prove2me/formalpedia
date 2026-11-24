-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DimensionInequalityOneGenerator_proof_93f0813fac2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:07:02.652832+00:00
-- url     : https://prove2.me/submissions/9807c4ef-6c16-4f91-912b-4f53b8b51a7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDimensionInequalitySteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimensionInequalityOneGenerator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
universe u v
open Polynomial Cardinal
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace DimensionInequalityOneGenerator
theorem _root_.solution (h₁ : PolynomialDimensionInequality.Statement.{u})
    (h₂ : QuotientHeightAddOne.Statement.{u}) : DimensionInequalityOneGenerator.Statement.{u, v} := by
  intro A B _ _ _ _ _ _ x hx hinj P _

  let φ : A[X] →ₐ[A] B := aeval x
  have hφ : Function.Surjective φ := by
    intro b
    have hb : b ∈ (aeval x : A[X] →ₐ[A] B).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, hx]; exact Algebra.mem_top
    exact hb

  let P' : Ideal A[X] := P.comap (φ : A[X] →+* B)
  have hP' : P.under A = P'.under A := by
    ext a; simp [P', φ, Ideal.under, Ideal.mem_comap]
  have : P'.LiesOver (P.under A) := ⟨hP'⟩

  have H₁ : ofENat P'.height + Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P') ≤
      ofENat (P.under A).height + 1 := by
    have key : ∀ (q : Ideal A) [q.IsPrime] [P'.LiesOver q],
        ofENat P'.height + Algebra.trdeg (A ⧸ q) (A[X] ⧸ P') ≤ ofENat q.height + 1 := by
      intro q _ _
      obtain rfl : q = P'.under A := Ideal.LiesOver.over
      exact h₁ A P'
    exact key _

  have htr : lift.{v} (Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P')) =
      lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) := by
    let f : A[X] ⧸ P' →+* B ⧸ P := Ideal.quotientMap P (φ : A[X] →+* B) le_rfl
    have hf : Function.Bijective f :=
      ⟨Ideal.quotientMap_injective' le_rfl, Ideal.quotientMap_surjective hφ⟩
    refine AlgEquiv.lift_trdeg_eq
      (AlgEquiv.ofRingEquiv (f := (RingEquiv.ofBijective f hf : A[X] ⧸ P' ≃+* B ⧸ P)) ?_)
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp [f, φ, Ideal.Quotient.algebraMap_mk_of_liesOver]

  have H₁' : ofENat P'.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) ≤
      ofENat (P.under A).height + 1 := by
    have := Cardinal.lift_le.{v}.mpr H₁
    simpa only [lift_add, lift_ofENat, lift_one, htr] using this
  rw [← Cardinal.lift_le.{u}]
  simp only [lift_add, lift_ofENat]
  by_cases hker : RingHom.ker φ = ⊥
  ·
    have hinjφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot _).mpr hker
    let e : A[X] ≃ₐ[A] B := AlgEquiv.ofBijective φ ⟨hinjφ, hφ⟩
    have hh : P'.height = P.height := RingEquiv.height_comap (e : A[X] ≃+* B) P
    have ht : lift.{u} (Algebra.trdeg A B) = 1 := by
      rw [← e.lift_trdeg_eq, Polynomial.trdeg_of_isDomain, lift_one]
    rw [ht, ← hh]
    exact H₁'
  ·
    let e := Ideal.quotientKerAlgEquivOfSurjective hφ
    let Q : Ideal (A[X] ⧸ RingHom.ker φ) := P.comap (e : A[X] ⧸ RingHom.ker φ ≃+* B)
    have hQ : Q.comap (Ideal.Quotient.mk (RingHom.ker φ)) = P' := by
      ext f; simp [Q, P', e, Ideal.mem_comap]
    have H₂ := h₂ A[X] (RingHom.ker φ) hker Q
    rw [hQ, RingEquiv.height_comap] at H₂
    have H : ofENat P.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) + 1 ≤
        ofENat (P.under A).height + 1 :=
      calc ofENat P.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) + 1
          = ofENat (P.height + 1) + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) := by
            rw [ofENat_add, ofENat_one]; ring
        _ ≤ ofENat P'.height + lift.{u} (Algebra.trdeg (A ⧸ P.under A) (B ⧸ P)) :=
            add_le_add (ofENat_le_ofENat.mpr H₂) le_rfl
        _ ≤ _ := H₁'
    exact (Cardinal.add_one_le_add_one_iff.mp H).trans le_self_add
end DimensionInequalityOneGenerator
end GroundTheory.Heights₂.Heights.NumbersDVR
