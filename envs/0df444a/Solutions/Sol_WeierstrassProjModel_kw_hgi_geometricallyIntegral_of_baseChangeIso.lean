-- Prove2me | solution 1 for WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b0a03dcd-0f9e-575c-896b-345220a8c73a

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_AlgebraicGeometry_ProjectiveWeierstrassPolynomialPrime
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.LocalProperties.Reduced
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial ProjWeierstrassCubicPrime

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SolRHgi

universe u

private scoped instance isReduced_homogeneousLocalization {ι A σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι]
    (𝒜 : ι → σ) [GradedRing 𝒜] (x : Submonoid A) [IsReduced A] :
    IsReduced (HomogeneousLocalization 𝒜 x) :=
  isReduced_of_injective (algebraMap (HomogeneousLocalization 𝒜 x) (Localization x))
    (HomogeneousLocalization.val_injective x)

private scoped instance isReduced_proj {σ : Type*} {A : Type u} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] [IsReduced A] :
    IsReduced (Proj 𝒜) := by
  haveI : ∀ i, IsReduced ((Proj.affineOpenCover 𝒜).openCover.X i) := fun i =>
    inferInstanceAs
      (IsReduced (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 (i.2 : A)))))
  exact IsReduced.of_openCover _ (Proj.affineOpenCover 𝒜).openCover

private scoped instance isClosedUnderIso_isIntegral :
    ObjectProperty.IsClosedUnderIsomorphisms (@AlgebraicGeometry.IsIntegral.{u}) where
  of_iso e hX := @IsIntegral.of_isIso _ _ hX e.hom inferInstance

variable {K : Type u} [Field K] (V : WeierstrassCurve.Projective K)

private scoped instance isDomain_projModelRingCR : IsDomain (ProjModelRingCR V) := by
  show IsDomain (MvPolynomial (Fin 3) K ⧸ (projModelHomogeneousIdealCR V).toIdeal)
  rw [projModelHomogeneousIdealCR_toIdeal]
  exact isDomain_quotient_span_polynomial V

private theorem X1_not_mem_spanCR :
    (X 1 : MvPolynomial (Fin 3) K) ∉ (projModelHomogeneousIdealCR V).toIdeal := by
  rw [projModelHomogeneousIdealCR_toIdeal, Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  have h0 : eval ![(0 : K), 1, 0] V.polynomial = 0 :=
    WeierstrassCurve.Projective.equation_zero (W' := V)
  have heval := congrArg (eval ![(0 : K), 1, 0]) hc
  rw [map_mul, h0, zero_mul, eval_X] at heval
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at heval
  exact one_ne_zero heval

private theorem mk_X1_ne_zeroCR :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
      (X 1 : MvPolynomial (Fin 3) K) ≠ 0 := fun h =>
  X1_not_mem_spanCR V (Ideal.Quotient.eq_zero_iff_mem.mp h)

private def genericPointCR : Proj (projModelGradingCR V) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    rw [HomogeneousIdeal.toIdeal_bot]
    exact Ideal.isPrime_bot
  not_irrelevant_le := fun hle => by
    have hmem : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X 1 : MvPolynomial (Fin 3) K)
          ∈ (⊥ : HomogeneousIdeal (projModelGradingCR V)).toIdeal :=
      hle (HomogeneousIdeal.mem_irrelevant_of_mem (𝒜 := projModelGradingCR V) one_pos
        (kw_pbac_mk_X_mem_one_CR K V 1))
    exact mk_X1_ne_zeroCR V
      (by first | exact Ideal.mem_bot.mp hmem | exact (Submodule.mem_bot _).mp hmem | simpa using hmem)

private theorem closure_genericPoint_eq_univCR :
    closure ({genericPointCR V} : Set (Proj (projModelGradingCR V))) = Set.univ :=
  Set.eq_univ_of_forall fun y =>
    (ProjectiveSpectrum.le_iff_mem_closure (𝒜 := projModelGradingCR V)
        (genericPointCR V) y).mp
      ((ProjectiveSpectrum.as_ideal_le_as_ideal (𝒜 := projModelGradingCR V)
          (genericPointCR V) y).mp bot_le)

private scoped instance irreducibleSpace_projModelCR : IrreducibleSpace (projModelCR V) where
  isPreirreducible_univ := by
    rw [← closure_genericPoint_eq_univCR V]
    exact isIrreducible_singleton.closure.isPreirreducible
  toNonempty := ⟨genericPointCR V⟩

private theorem isIntegral_projModelCR_field : IsIntegral (projModelCR V) :=
  isIntegral_of_irreducibleSpace_of_isReduced (projModelCR V)

end SolRHgi
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso.SolRHgi"

open SolRHgi in
theorem solution.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
      Nonempty (pullback (projModelStrCR W.toProjective)
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ≅ projModelCR (W.toProjective.baseChange K))) :
    GeometricallyIntegral (projModelStrCR W.toProjective) := by
  constructor
  rw [AlgebraicGeometry.geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  obtain ⟨e⟩ := hbc K
  exact ObjectProperty.prop_of_iso (@AlgebraicGeometry.IsIntegral) e.symm
    (isIntegral_projModelCR_field (W.map (algebraMap R K)).toProjective)

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso.SolRHgi"

end S_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
end P2MW
export P2MW.S_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso (solution)
