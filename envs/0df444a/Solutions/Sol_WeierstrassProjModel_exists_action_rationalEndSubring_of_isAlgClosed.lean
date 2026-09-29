-- Prove2me | solution 1 for WeierstrassProjModel.exists_action_rationalEndSubring_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/50780e28-eb96-5841-8e89-567e3d2e7ff0

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_JacJ1Iface
import Theorems.Thm_WeierstrassProjModel_exists_schemeHomOver_forall_apply_eq_of_isRationallyRepresented_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_point_of_isReduced_of_locallyOfFiniteType
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smooth
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassCurve_mem_rationalEndSubring_iff_mem_rationalHomSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_action_rationalEndSubring_of_isAlgClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry WeierstrassCurve.DrinfeldGlobal

noncomputable section

namespace EndBridgeSol

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

scoped instance isReduced_E : IsReduced (E X) := inferInstance

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

theorem comp_one {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (P : SchemeHomOver t (π X)) :
    NeronModelInfra.schemeHomOverComp P (G.one (π X)) = G.one t := by
  rw [comp_eq_transition]
  exact G.one_natural (π X) t P.1 P.2

include hev_add in
theorem ev_one : ev (G.one (t₀ k)) = 0 := by
  have h := hev_add (G.one (t₀ k)) (G.one (t₀ k))
  rw [G.one_mul] at h
  exact left_eq_add.mp h

theorem eq_of_forall_ev_eq (φ ψ : SchemeHomOver (π X) (π X))
    (h : ∀ P : SchemeHomOver (t₀ k) (π X),
      ev (NeronModelInfra.schemeHomOverComp P φ) = ev (NeronModelInfra.schemeHomOverComp P ψ)) :
    φ = ψ := by
  refine AlgebraicGeometry.SchemeHomOver.ext_of_forall_point_of_isReduced_of_locallyOfFiniteType k φ ψ ?_
  intro x
  have := h ⟨x.1, x.2.trans (t₀_eq k).symm⟩
  exact congrArg Subtype.val (ev.injective this)

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

include hev_add in

theorem pointed (φ : SchemeHomOver (π X) (π X)) (α : AddMonoid.End (X.baseChange k).toAffine.Point)
    (hφ : ∀ P : SchemeHomOver (t₀ k) (π X), ev (NeronModelInfra.schemeHomOverComp P φ) = α (ev P)) :
    NeronModelInfra.schemeHomOverComp ((toGRJ X G).one (𝟙 _)) φ = (toGRJ X G).one (𝟙 _) := by
  change NeronModelInfra.schemeHomOverComp (G.one (𝟙 _)) φ = G.one (𝟙 _)
  apply toT₀_injective
  rw [toT₀_comp, toT₀_one]
  apply ev.injective
  rw [hφ, ev_one G ev hev_add]
  exact map_zero α

include hev_add in

theorem isHom (φ : SchemeHomOver (π X) (π X)) (α : AddMonoid.End (X.baseChange k).toAffine.Point)
    (hφ : ∀ P : SchemeHomOver (t₀ k) (π X), ev (NeronModelInfra.schemeHomOverComp P φ) = α (ev P))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t (π X)) :
    NeronModelInfra.schemeHomOverComp (G.mul t P Q) φ =
      G.mul t (NeronModelInfra.schemeHomOverComp P φ) (NeronModelInfra.schemeHomOverComp Q φ) :=
  GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
    k (toGRJ X G) (toGRJ X G) (bundle X G) φ (pointed G ev hev_add φ α hφ) t P Q

def Induces (φ : SchemeHomOver (π X) (π X)) (α : AddMonoid.End (X.baseChange k).toAffine.Point) : Prop :=
  ∀ P : SchemeHomOver (t₀ k) (π X), ev (NeronModelInfra.schemeHomOverComp P φ) = α (ev P)

include hev_add in
theorem induces_zero : Induces ev (G.one (π X)) 0 := by
  intro P
  rw [comp_one, ev_one G ev hev_add]
  rfl

theorem induces_one : Induces ev (NeronModelInfra.schemeHomOverId (π X)) 1 := by
  intro P
  rw [NeronModelInfra.schemeHomOverComp_id_right]
  rfl

theorem induces_mul {φ ψ : SchemeHomOver (π X) (π X)} {α β : AddMonoid.End (X.baseChange k).toAffine.Point}
    (hφ : Induces ev φ α) (hψ : Induces ev ψ β) :
    Induces ev (NeronModelInfra.schemeHomOverComp ψ φ) (α * β) := by
  intro P
  rw [← NeronModelInfra.schemeHomOverComp_assoc, hφ, hψ]
  rfl

include hev_add in
theorem induces_add {φ ψ : SchemeHomOver (π X) (π X)} {α β : AddMonoid.End (X.baseChange k).toAffine.Point}
    (hφ : Induces ev φ α) (hψ : Induces ev ψ β) :
    Induces ev (G.mul (π X) φ ψ) (α + β) := by
  intro P
  rw [comp_mul, hev_add, hφ, hψ]
  rfl

theorem induces_unique {φ ψ : SchemeHomOver (π X) (π X)} {α : AddMonoid.End (X.baseChange k).toAffine.Point}
    (hφ : Induces ev φ α) (hψ : Induces ev ψ α) : φ = ψ :=
  eq_of_forall_ev_eq ev φ ψ fun P => (hφ P).trans (hψ P).symm

end Main

end EndBridgeSol
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_action_rationalEndSubring_of_isAlgClosed.EndBridgeSol"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_action_rationalEndSubring_of_isAlgClosed.EndBridgeSol"

open EndBridgeSol NeronModelInfra WeierstrassProjModel

theorem solution
    {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
    (X : WeierstrassCurve k) [X.IsElliptic]
    (G : WeierstrassProjModel.RelativeGroupLaw k (projModelStrCR X.toProjective))
    (ev : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) (projModelStrCR X.toProjective) ≃
      (X.toProjective.baseChange k).toAffine.Point)
    (hev_add : ∀ P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) (projModelStrCR X.toProjective),
      ev (G.mul (Spec.map (CommRingCat.ofHom (algebraMap k k))) P Q) = ev P + ev Q)
    (hev_chart : ∀ (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) (projModelStrCR X.toProjective))
        (χ : ZChartRing X.toProjective →+* k),
      P.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι X.toProjective →
      ∃ hxy : (X.toProjective.baseChange k).toAffine.Nonsingular (χ (xOverZ X.toProjective)) (χ (yOverZ X.toProjective)),
        ev P = WeierstrassCurve.Affine.Point.some _ _ hxy) :
    ∃ Φ : ↥(WeierstrassCurve.rationalEndSubring k X) →
        SchemeHomOver (projModelStrCR X.toProjective) (projModelStrCR X.toProjective),
      (∀ (α : ↥(WeierstrassCurve.rationalEndSubring k X))
          (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) (projModelStrCR X.toProjective)),
        ev (NeronModelInfra.schemeHomOverComp P (Φ α)) =
          (α : AddMonoid.End (X.baseChange k).toAffine.Point) (ev P)) ∧
      (∀ (α : ↥(WeierstrassCurve.rationalEndSubring k X)) {T : Scheme.{0}}
          (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t (projModelStrCR X.toProjective)),
        NeronModelInfra.schemeHomOverComp (G.mul t P Q) (Φ α) =
          G.mul t (NeronModelInfra.schemeHomOverComp P (Φ α)) (NeronModelInfra.schemeHomOverComp Q (Φ α))) ∧
      Φ 1 = NeronModelInfra.schemeHomOverId (projModelStrCR X.toProjective) ∧
      (∀ α β : ↥(WeierstrassCurve.rationalEndSubring k X),
        Φ (α * β) = NeronModelInfra.schemeHomOverComp (Φ β) (Φ α)) ∧
      (∀ (α β : ↥(WeierstrassCurve.rationalEndSubring k X)) {T : Scheme.{0}}
          (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t (projModelStrCR X.toProjective)),
        NeronModelInfra.schemeHomOverComp P (Φ (α + β)) =
          G.mul t (NeronModelInfra.schemeHomOverComp P (Φ α)) (NeronModelInfra.schemeHomOverComp P (Φ β))) := by

  have hex : ∀ α : ↥(WeierstrassCurve.rationalEndSubring k X),
      ∃ φ : SchemeHomOver (projModelStrCR X.toProjective) (projModelStrCR X.toProjective),
        Induces ev φ (α : AddMonoid.End (X.baseChange k).toAffine.Point) := by
    intro α
    have hmem := (WeierstrassCurve.mem_rationalEndSubring_iff_mem_rationalHomSet k X
      (α : AddMonoid.End (X.baseChange k).toAffine.Point)).mp α.2
    rcases hmem with h0 | hrr
    · refine ⟨G.one _, fun P => ?_⟩
      rw [induces_zero G ev hev_add P]
      have : (α : AddMonoid.End (X.baseChange k).toAffine.Point) = 0 := by
        ext x; exact DFunLike.congr_fun h0 x
      rw [this]
    · obtain ⟨φ, hφ⟩ :=
        WeierstrassProjModel.exists_schemeHomOver_forall_apply_eq_of_isRationallyRepresented_of_isAlgClosed
          X G ev hev_add hev_chart _ hrr
      exact ⟨φ, fun P => hφ P⟩
  choose Φ hΦ using hex
  refine ⟨Φ, fun α P => hΦ α P, fun α {T} t P Q => isHom G ev hev_add (Φ α) _ (hΦ α) t P Q, ?_, ?_, ?_⟩
  · exact induces_unique ev (hΦ 1) (induces_one ev)
  · intro α β
    exact induces_unique ev (hΦ (α * β)) (induces_mul ev (hΦ α) (hΦ β))
  · intro α β T t P
    have h : Φ (α + β) = G.mul _ (Φ α) (Φ β) :=
      induces_unique ev (hΦ (α + β)) (induces_add G ev hev_add (hΦ α) (hΦ β))
    rw [h, comp_mul]

end S_WeierstrassProjModel_exists_action_rationalEndSubring_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassProjModel_exists_action_rationalEndSubring_of_isAlgClosed (solution)
