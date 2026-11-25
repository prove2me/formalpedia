-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__Conormal_finite_projective_cotangent_6ff6ba17bbab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:52:42.157787+00:00
-- url     : https://prove2.me/submissions/66913392-1d39-4c64-a3a6-745e6e539a79

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalFiniteProjectiveOfSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
open TensorProduct
namespace GlobalTheory.CompanionTheory.Hypotheses₂.Conormal
theorem _root_.solution :
    ∀ {k A : Type} [Field k] [CommRing A] (φ : k →+* A) (I : Ideal A), φ.Smooth →
      ((Ideal.Quotient.mk I).comp φ).Smooth →
        Module.Finite (A ⧸ I) I.Cotangent ∧ Module.Projective (A ⧸ I) I.Cotangent := by
  intro k A _ _ φ I h1 h2
  letI := φ.toAlgebra
  haveI hA : Algebra.Smooth k A := h1
  have halg : (Ideal.Quotient.algebra k : Algebra k (A ⧸ I)) =
      ((Ideal.Quotient.mk I).comp φ).toAlgebra := Algebra.algebra_ext _ _ fun _ => rfl
  have hQ : Algebra.FormallySmooth k (A ⧸ I) := by
    have hs : @Algebra.Smooth k _ (A ⧸ I) _ ((Ideal.Quotient.mk I).comp φ).toAlgebra := h2
    rw [← halg] at hs
    exact hs.formallySmooth
  haveI : Algebra.FormallySmooth k A := hA.formallySmooth
  haveI : Module.Projective A (KaehlerDifferential k A) :=
    Algebra.FormallySmooth.projective_kaehlerDifferential
  haveI : Algebra.FinitePresentation k A := hA.finitePresentation
  haveI : Algebra.FiniteType k A := Algebra.FiniteType.of_finitePresentation
  haveI : Algebra.EssFiniteType k A := Algebra.EssFiniteType.of_finiteType k A
  haveI : Module.Finite A (KaehlerDifferential k A) := KaehlerDifferential.finite k A
  haveI : Module.Finite (A ⧸ I) ((A ⧸ I) ⊗[A] KaehlerDifferential k A) :=
    Module.Finite.base_change A (A ⧸ I) _
  haveI : IsScalarTower A (A ⧸ I) I.Cotangent := by
    first
    | infer_instance
    | exact IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k) (P := A) (A := A ⧸ I)
    Ideal.Quotient.mk_surjective).mp hQ
  have hsurj : Function.Surjective (algebraMap A (A ⧸ I)) := Ideal.Quotient.mk_surjective
  let e := Ideal.Cotangent.equivOfEq _ _ (Ideal.mk_ker (I := I))
  let i : I.Cotangent →ₗ[A ⧸ I] (A ⧸ I) ⊗[A] KaehlerDifferential k A :=
    LinearMap.extendScalarsOfSurjective hsurj
      (KaehlerDifferential.kerCotangentToTensor k A (A ⧸ I) ∘ₗ e.symm.toLinearMap)
  let s : (A ⧸ I) ⊗[A] KaehlerDifferential k A →ₗ[A ⧸ I] I.Cotangent :=
    LinearMap.extendScalarsOfSurjective hsurj (e.toLinearMap ∘ₗ l)
  have hsi : s ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    have h := LinearMap.congr_fun hl (e.symm x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
    first
    | (simp only [s, i, LinearMap.comp_apply, LinearMap.extendScalarsOfSurjective_apply,
        LinearEquiv.coe_coe, LinearMap.id_apply, h, LinearEquiv.apply_symm_apply]; done)
    | (show e (l (KaehlerDifferential.kerCotangentToTensor k A (A ⧸ I) (e.symm x))) = x
       rw [h, LinearEquiv.apply_symm_apply])
  refine ⟨Module.Finite.of_surjective s fun x => ⟨i x, ?_⟩, Module.Projective.of_split i s hsi⟩
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using LinearMap.congr_fun hsi x
end GlobalTheory.CompanionTheory.Hypotheses₂.Conormal
