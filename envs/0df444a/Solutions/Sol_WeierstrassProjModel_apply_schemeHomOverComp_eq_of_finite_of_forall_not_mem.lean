-- Prove2me | solution 1 for WeierstrassProjModel.apply_schemeHomOverComp_eq_of_finite_of_forall_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a3918665-1fcc-5c07-9988-6e0ec765c3aa

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_JacJ1Iface
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smooth
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_apply_schemeHomOverComp_eq_of_finite_of_forall_not_mem
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace P2mCofinite

open NeronModelInfra (SchemeHomOver)

section Setup

variable {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
variable (X : WeierstrassCurve k) [X.IsElliptic]

abbrev E : Scheme.{0} := WeierstrassProjModel.projModelCR X.toProjective

abbrev π : E X ⟶ Spec (CommRingCat.of k) := WeierstrassProjModel.projModelStrCR X.toProjective

abbrev t₀ (k : Type) [Field k] : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k))

theorem t₀_eq (k : Type) [Field k] : t₀ k = 𝟙 _ := by
  simp only [t₀, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

scoped instance isProper_π : IsProper (π X) := WeierstrassProjModel.projModelStrCR_isProper X.toProjective

scoped instance smooth_π : Smooth (π X) := WeierstrassProjModel.projModelStrCR_smooth X.toProjective

scoped instance geometricallyIntegral_π : GeometricallyIntegral (π X) :=
  WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso X
    (WeierstrassProjModel.projModel_pullback_iso_baseChange X.toProjective)

scoped instance subsingleton_specField : Subsingleton (Spec (CommRingCat.of k) : Scheme.{0}) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

scoped instance isIntegral_E : IsIntegral (E X) :=
  GeometricallyIntegral.isIntegral_of_subsingleton (π X)

scoped instance connectedSpace_E : ConnectedSpace (E X) := inferInstance

theorem bundle (G : WeierstrassProjModel.RelativeGroupLaw k (π X)) :
    GoodReductionJacobian.AbelianSchemePropertyBundle k (π X) where
  smooth := inferInstance
  proper := inferInstance
  connectedFibres s := by
    have : (π X).base ⁻¹' {s} = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [this]
    exact isConnected_univ
  hasGroupLaw := ⟨
    { mul := G.mul, one := G.one, inv := G.inv, mul_assoc := G.mul_assoc, one_mul := G.one_mul,
      mul_one := G.mul_one, inv_mul_cancel := G.inv_mul_cancel,
      mul_natural := fun t t' ψ hψ x y => G.mul_natural t t' ψ hψ x y }⟩

def toGRJ (G : WeierstrassProjModel.RelativeGroupLaw k (π X)) :
    GoodReductionJacobian.RelativeGroupLaw k (π X) where
  mul := G.mul
  one := G.one
  inv := G.inv
  mul_assoc := G.mul_assoc
  one_mul := G.one_mul
  mul_one := G.mul_one
  inv_mul_cancel := G.inv_mul_cancel
  mul_natural := fun t t' ψ hψ x y => G.mul_natural t t' ψ hψ x y

end Setup

section Main

variable {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
variable {X : WeierstrassCurve k} [X.IsElliptic]
variable (G : WeierstrassProjModel.RelativeGroupLaw k (π X))
variable (ev : SchemeHomOver (t₀ k) (π X) ≃ (X.toProjective.baseChange k).toAffine.Point)
variable (hev_add : ∀ P Q : SchemeHomOver (t₀ k) (π X), ev (G.mul (t₀ k) P Q) = ev P + ev Q)

theorem comp_eq_transition {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)}
    (P : SchemeHomOver t (π X)) (φ : SchemeHomOver (π X) (π X)) :
    NeronModelInfra.schemeHomOverComp P φ = WeierstrassProjModel.schemeHomOverComp P.1 P.2 φ :=
  Subtype.ext rfl

theorem comp_mul {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)}
    (P : SchemeHomOver t (π X)) (φ ψ : SchemeHomOver (π X) (π X)) :
    NeronModelInfra.schemeHomOverComp P (G.mul (π X) φ ψ) =
      G.mul t (NeronModelInfra.schemeHomOverComp P φ) (NeronModelInfra.schemeHomOverComp P ψ) := by
  simp only [comp_eq_transition]
  exact G.mul_natural (π X) t P.1 P.2 φ ψ

include hev_add in
theorem ev_one : ev (G.one (t₀ k)) = 0 := by
  have h := hev_add (G.one (t₀ k)) (G.one (t₀ k))
  rw [G.one_mul] at h
  exact left_eq_add.mp h

include hev_add in
theorem ev_inv (P : SchemeHomOver (t₀ k) (π X)) : ev (G.inv (t₀ k) P) = -ev P := by
  have h := hev_add (G.inv (t₀ k) P) P
  rw [G.inv_mul_cancel, ev_one G ev hev_add] at h
  exact (neg_eq_of_add_eq_zero_left h.symm).symm

def constEnd (Q : SchemeHomOver (t₀ k) (π X)) : SchemeHomOver (π X) (π X) :=
  ⟨π X ≫ Q.1, by rw [Category.assoc, Q.2, t₀_eq, Category.comp_id]⟩

theorem comp_constEnd (P Q : SchemeHomOver (t₀ k) (π X)) :
    NeronModelInfra.schemeHomOverComp P (constEnd Q) = Q := by
  apply Subtype.ext
  change P.1 ≫ (π X ≫ Q.1) = Q.1
  rw [← Category.assoc, P.2]
  have key : ∀ (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)), s = 𝟙 _ →
      ∀ q : Spec (CommRingCat.of k) ⟶ E X, s ≫ q = q := by
    rintro s rfl q; exact Category.id_comp q
  exact key _ (t₀_eq k) Q.1

def toT₀ (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (π X)) : SchemeHomOver (t₀ k) (π X) :=
  ⟨Q.1, Q.2.trans (t₀_eq k).symm⟩

theorem toT₀_injective : Function.Injective (toT₀ (X := X)) := by
  intro Q Q' h
  have h' : (toT₀ Q).1 = (toT₀ Q').1 := congrArg Subtype.val h
  exact Subtype.ext h'

theorem toT₀_one : toT₀ (G.one (𝟙 _)) = G.one (t₀ k) := by
  have h := G.one_natural (𝟙 (Spec (CommRingCat.of k))) (t₀ k) (𝟙 _)
    (by rw [Category.id_comp, t₀_eq])
  refine (Subtype.ext ?_).trans h
  simp only [toT₀, WeierstrassProjModel.schemeHomOverComp_coe, Category.id_comp]

theorem toT₀_comp (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (π X)) (φ : SchemeHomOver (π X) (π X)) :
    toT₀ (NeronModelInfra.schemeHomOverComp Q φ) = NeronModelInfra.schemeHomOverComp (toT₀ Q) φ :=
  Subtype.ext rfl

include ev in

theorem infinite_points : Infinite (SchemeHomOver (t₀ k) (π X)) := by
  classical
  haveI : Infinite k := inferInstance

  let W : WeierstrassCurve.Affine k := (X.toProjective.baseChange k).toAffine
  haveI hW : WeierstrassCurve.IsElliptic (X.toProjective.baseChange k) := by
    change WeierstrassCurve.IsElliptic (X.map (algebraMap k k)); infer_instance
  have hpt : ∀ x : k, ∃ y : k, W.Nonsingular x y := by
    intro x

    let p : Polynomial k := Polynomial.X ^ 2 + Polynomial.C (W.a₁ * x + W.a₃) * Polynomial.X -
      Polynomial.C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    have hp : p.degree = 2 := by
      simp only [p]
      compute_degree!
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root p (by rw [hp]; decide)
    refine ⟨y, (WeierstrassCurve.Affine.equation_iff_nonsingular (W := W)).1 ?_⟩
    rw [WeierstrassCurve.Affine.equation_iff]
    have : Polynomial.eval y p = 0 := hy
    simp only [p, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C] at this
    linear_combination this
  choose y hy using hpt
  let f : k → SchemeHomOver (t₀ k) (π X) := fun x => ev.symm (WeierstrassCurve.Affine.Point.some x (y x) (hy x))
  refine Infinite.of_injective f fun x x' h => ?_
  have h' := ev.symm.injective h
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at h'
  exact h'.1

include hev_add in

theorem main (α : (X.baseChange k).toAffine.Point →+ (X.baseChange k).toAffine.Point)
    (φ : SchemeHomOver (π X) (π X)) (S : Set (SchemeHomOver (t₀ k) (π X))) (hS : S.Finite)
    (hφ : ∀ P : SchemeHomOver (t₀ k) (π X), P ∉ S → ev (NeronModelInfra.schemeHomOverComp P φ) = α (ev P))
    (P : SchemeHomOver (t₀ k) (π X)) :
    ev (NeronModelInfra.schemeHomOverComp P φ) = α (ev P) := by
  classical
  haveI := infinite_points (X := X) ev

  set O : SchemeHomOver (t₀ k) (π X) := G.one (t₀ k) with hO
  set c := ev (NeronModelInfra.schemeHomOverComp O φ) with hc
  let φ' : SchemeHomOver (π X) (π X) :=
    G.mul (π X) φ (constEnd (G.inv (t₀ k) (NeronModelInfra.schemeHomOverComp O φ)))
  have hφ' : ∀ Q : SchemeHomOver (t₀ k) (π X),
      ev (NeronModelInfra.schemeHomOverComp Q φ') = ev (NeronModelInfra.schemeHomOverComp Q φ) - c := by
    intro Q
    simp only [φ']
    rw [comp_mul, hev_add, comp_constEnd, ev_inv G ev hev_add, hc, sub_eq_add_neg]

  have hpt : NeronModelInfra.schemeHomOverComp ((toGRJ X G).one (𝟙 _)) φ' = (toGRJ X G).one (𝟙 _) := by
    change NeronModelInfra.schemeHomOverComp (G.one (𝟙 _)) φ' = G.one (𝟙 _)
    apply toT₀_injective
    rw [toT₀_comp, toT₀_one]
    apply ev.injective
    rw [hφ', ← hO, ← hc, sub_self, ev_one G ev hev_add]

  have hadd : ∀ Q R : SchemeHomOver (t₀ k) (π X),
      ev (NeronModelInfra.schemeHomOverComp (G.mul (t₀ k) Q R) φ) =
        ev (NeronModelInfra.schemeHomOverComp Q φ) + ev (NeronModelInfra.schemeHomOverComp R φ) - c := by
    intro Q R
    have h := GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
      k (toGRJ X G) (toGRJ X G) (bundle X G) φ' hpt (t₀ k) Q R
    change NeronModelInfra.schemeHomOverComp (G.mul (t₀ k) Q R) φ' =
      G.mul (t₀ k) (NeronModelInfra.schemeHomOverComp Q φ') (NeronModelInfra.schemeHomOverComp R φ') at h
    have h' := congrArg ev h
    rw [hev_add, hφ', hφ', hφ'] at h'

    have := h'
    abel_nf at this ⊢
    linear_combination (norm := abel_nf) h'

  have hinj : ∀ R : SchemeHomOver (t₀ k) (π X), Function.Injective fun Q => G.mul (t₀ k) Q R := by
    intro R Q Q' h
    have h' := congrArg ev h
    simp only [hev_add] at h'
    exact ev.injective (add_right_cancel h')
  have hgood : ∀ R : SchemeHomOver (t₀ k) (π X), ∃ Q : SchemeHomOver (t₀ k) (π X),
      Q ∉ S ∧ G.mul (t₀ k) Q R ∉ S := by
    intro R
    have hfin : (S ∪ (fun Q => G.mul (t₀ k) Q R) ⁻¹' S).Finite :=
      hS.union (hS.preimage (hinj R).injOn)
    obtain ⟨Q, hQ⟩ := hfin.infinite_compl.nonempty
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_preimage, not_or] at hQ
    exact ⟨Q, hQ.1, hQ.2⟩

  have hc0 : c = 0 := by
    obtain ⟨R, hR⟩ := hS.infinite_compl.nonempty
    obtain ⟨Q, hQ, hQR⟩ := hgood R
    have h1 := hadd Q R
    rw [hφ _ hQR, hφ _ hQ, hφ _ hR, hev_add, map_add] at h1

    have : (0 : (X.toProjective.baseChange k).toAffine.Point) = -c := by
      linear_combination (norm := abel_nf) h1
    rw [eq_comm, neg_eq_zero] at this
    exact this

  obtain ⟨Q, hQ, hQP⟩ := hgood P
  have h1 := hadd Q P
  rw [hc0, sub_zero, hφ _ hQP, hφ _ hQ, hev_add, map_add] at h1
  exact (add_left_cancel h1).symm

end Main

end P2mCofinite
p2m_reactivate "P2MW.S_WeierstrassProjModel_apply_schemeHomOverComp_eq_of_finite_of_forall_not_mem.P2mCofinite"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_apply_schemeHomOverComp_eq_of_finite_of_forall_not_mem.P2mCofinite"

open P2mCofinite NeronModelInfra WeierstrassProjModel

theorem solution
    {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
    (X : WeierstrassCurve k) [X.IsElliptic]
    (G : WeierstrassProjModel.RelativeGroupLaw k (WeierstrassProjModel.projModelStrCR X.toProjective))
    (ev : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k)))
        (WeierstrassProjModel.projModelStrCR X.toProjective) ≃
      (X.toProjective.baseChange k).toAffine.Point)
    (hev_add : ∀ P Q : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k)))
        (WeierstrassProjModel.projModelStrCR X.toProjective),
      ev (G.mul (Spec.map (CommRingCat.ofHom (algebraMap k k))) P Q) = ev P + ev Q)
    (α : (X.baseChange k).toAffine.Point →+ (X.baseChange k).toAffine.Point)
    (φ : NeronModelInfra.SchemeHomOver (WeierstrassProjModel.projModelStrCR X.toProjective)
        (WeierstrassProjModel.projModelStrCR X.toProjective))
    (S : Set (NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k)))
        (WeierstrassProjModel.projModelStrCR X.toProjective)))
    (hS : S.Finite)
    (hφ : ∀ P : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k)))
        (WeierstrassProjModel.projModelStrCR X.toProjective),
      P ∉ S → ev (NeronModelInfra.schemeHomOverComp P φ) = α (ev P)) :
    ∀ P : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k)))
        (WeierstrassProjModel.projModelStrCR X.toProjective),
      ev (NeronModelInfra.schemeHomOverComp P φ) = α (ev P) :=
  fun P => main G ev hev_add α φ S hS hφ P

end S_WeierstrassProjModel_apply_schemeHomOverComp_eq_of_finite_of_forall_not_mem
end P2MW
export P2MW.S_WeierstrassProjModel_apply_schemeHomOverComp_eq_of_finite_of_forall_not_mem (solution)
