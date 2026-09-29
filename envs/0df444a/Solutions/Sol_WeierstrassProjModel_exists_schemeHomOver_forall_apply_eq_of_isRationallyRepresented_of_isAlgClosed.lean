-- Prove2me | solution 1 for WeierstrassProjModel.exists_schemeHomOver_forall_apply_eq_of_isRationallyRepresented_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fcdf9d28-ccf6-57d1-be9b-4486b25f92f0

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_JacJ1Iface
import Theorems.Thm_WeierstrassProjModel_apply_schemeHomOverComp_eq_of_finite_of_forall_not_mem
import Theorems.Thm_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle
import Theorems.Thm_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smooth
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_schemeHomOver_forall_apply_eq_of_isRationallyRepresented_of_isAlgClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longFile 0
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial"
open scoped Polynomial.Bivariate

noncomputable section

namespace P2mExtension

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

scoped instance irreducibleSpace_E : IrreducibleSpace (E X) := inferInstance

scoped instance isSeparated_π : IsSeparated (π X) := inferInstance

scoped instance quasiCompact_π : QuasiCompact (π X) := inferInstance

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

end Setup

section Algebra

variable {k : Type} [Field k]

theorem mk_eq_zero_of_infinite (W : WeierstrassCurve.Affine k) (g : k[X][Y])
    (h : {x : k | ∃ y : k, W.Equation x y ∧ g.evalEval x y = 0}.Infinite) :
    WeierstrassCurve.Affine.CoordinateRing.mk W g = 0 := by
  classical
  haveI : Module.Free k[X] W.CoordinateRing :=
    Module.Free.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W)
  haveI : Module.Finite k[X] W.CoordinateRing :=
    Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W)
  by_contra hne
  obtain ⟨p, q, hpq⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq
    (WeierstrassCurve.Affine.CoordinateRing.mk W g)
  set N : k[X] := Algebra.norm k[X] (WeierstrassCurve.Affine.CoordinateRing.mk W g) with hN_def
  have hN : N ≠ 0 := Algebra.norm_ne_zero_iff.2 hne
  have hNa : (algebraMap k[X] W.CoordinateRing N) =
      WeierstrassCurve.Affine.CoordinateRing.mk W g *
        WeierstrassCurve.Affine.CoordinateRing.mk W (C p + C q * (-(Y : k[X][Y]) - C (C W.a₁ * X + C W.a₃))) := by
    have h1 := WeierstrassCurve.Affine.CoordinateRing.coe_norm_smul_basis (W' := W) p q
    rw [hpq] at h1
    rw [hN_def]
    refine h1.trans ?_
    rw [map_mul]
    congr 1
    rw [← hpq, map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, Algebra.smul_def, Algebra.smul_def, mul_one]
    rfl
  have hroot : {x : k | ∃ y : k, W.Equation x y ∧ g.evalEval x y = 0} ⊆ {x | N.IsRoot x} := by
    rintro x ⟨y, hxy, hg⟩
    have hW : W.polynomial.evalEval x y = 0 := hxy
    let φ : W.CoordinateRing →+* k := AdjoinRoot.evalEval hW
    have hφg : φ (WeierstrassCurve.Affine.CoordinateRing.mk W g) = 0 := by
      show AdjoinRoot.evalEval hW (AdjoinRoot.mk W.polynomial g) = 0
      rw [AdjoinRoot.evalEval_mk]; exact hg
    have hφN : φ (algebraMap k[X] W.CoordinateRing N) = N.eval x := by
      show AdjoinRoot.lift (evalRingHom x) y _ (AdjoinRoot.of W.polynomial N) = _
      rw [AdjoinRoot.lift_of]; rfl
    show N.IsRoot x
    rw [IsRoot.def, ← hφN, hNa, map_mul, hφg, zero_mul]
  exact h (Set.Finite.subset (Polynomial.finite_setOf_isRoot hN) hroot)

theorem exists_nonsingular [IsAlgClosed k] (W : WeierstrassCurve.Affine k) [W.IsElliptic] (x : k) :
    ∃ y : k, W.Nonsingular x y := by
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

theorem finite_setOf_point_eq_some [DecidableEq k] (W : WeierstrassCurve.Affine k) (x : k) :
    {Q : W.Point | ∃ (y : k) (h : W.Nonsingular x y), Q = .some x y h}.Finite := by
  classical
  let p : Polynomial k := Polynomial.X ^ 2 + Polynomial.C (W.a₁ * x + W.a₃) * Polynomial.X -
    Polynomial.C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
  have hp : p ≠ 0 := by
    have : p.degree = 2 := by
      simp only [p]
      compute_degree!
    intro h0; rw [h0, Polynomial.degree_zero] at this; exact absurd this (by decide)
  let mkPt : k → W.Point := fun y => if h : W.Nonsingular x y then .some x y h else 0
  refine ((p.roots.toFinset.finite_toSet).image mkPt).subset ?_
  rintro Q ⟨y, h, rfl⟩
  refine ⟨y, ?_, by simp only [mkPt, dif_pos h]⟩
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
  have he := (WeierstrassCurve.Affine.equation_iff (W := W) x y).1 h.1
  simp only [p, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C]
  linear_combination he

theorem clear_denominators {L : Type*} [CommRing L] (a₁ a₂ a₃ a₄ a₆ nx dx ny dy ix iy : L)
    (hx : ix * dx = 1) (hy : iy * dy = 1) :
    ((ny * iy) ^ 2 + a₁ * (nx * ix) * (ny * iy) + a₃ * (ny * iy)
        - ((nx * ix) ^ 3 + a₂ * (nx * ix) ^ 2 + a₄ * (nx * ix) + a₆)) * (dx ^ 3 * dy ^ 2) =
      ny ^ 2 * dx ^ 3 + a₁ * nx * ny * dx ^ 2 * dy + a₃ * ny * dx ^ 3 * dy
        - (nx ^ 3 * dy ^ 2 + a₂ * nx ^ 2 * dx * dy ^ 2 + a₄ * nx * dx ^ 2 * dy ^ 2 + a₆ * dx ^ 3 * dy ^ 2) := by
  linear_combination
    (a₁ * nx * ny * dx ^ 2 * dy * (iy * dy) - nx ^ 3 * dy ^ 2 * ((ix * dx) ^ 2 + ix * dx + 1)
      - a₂ * nx ^ 2 * dx * dy ^ 2 * (ix * dx + 1) - a₄ * nx * dx ^ 2 * dy ^ 2) * hx
    + (ny ^ 2 * dx ^ 3 * (iy * dy + 1) + a₁ * nx * ny * dx ^ 2 * dy + a₃ * ny * dx ^ 3 * dy) * hy

def clearedPoly (W : WeierstrassCurve.Affine k) (nX dX nY dY : k[X][Y]) : k[X][Y] :=
  nY ^ 2 * dX ^ 3 + C (C W.a₁) * nX * nY * dX ^ 2 * dY + C (C W.a₃) * nY * dX ^ 3 * dY
    - (nX ^ 3 * dY ^ 2 + C (C W.a₂) * nX ^ 2 * dX * dY ^ 2 + C (C W.a₄) * nX * dX ^ 2 * dY ^ 2
      + C (C W.a₆) * dX ^ 3 * dY ^ 2)

theorem evalEval_clearedPoly (W : WeierstrassCurve.Affine k) (nX dX nY dY : k[X][Y]) (x y : k) :
    (clearedPoly W nX dX nY dY).evalEval x y =
      (nY.evalEval x y) ^ 2 * (dX.evalEval x y) ^ 3
        + W.a₁ * nX.evalEval x y * nY.evalEval x y * (dX.evalEval x y) ^ 2 * dY.evalEval x y
        + W.a₃ * nY.evalEval x y * (dX.evalEval x y) ^ 3 * dY.evalEval x y
        - ((nX.evalEval x y) ^ 3 * (dY.evalEval x y) ^ 2
          + W.a₂ * (nX.evalEval x y) ^ 2 * dX.evalEval x y * (dY.evalEval x y) ^ 2
          + W.a₄ * nX.evalEval x y * (dX.evalEval x y) ^ 2 * (dY.evalEval x y) ^ 2
          + W.a₆ * (dX.evalEval x y) ^ 3 * (dY.evalEval x y) ^ 2) := by
  simp only [clearedPoly, evalEval_sub, evalEval_add, evalEval_mul, evalEval_pow, evalEval_CC]

theorem evalEval_clearedPoly_eq_zero (W : WeierstrassCurve.Affine k) (nX dX nY dY : k[X][Y]) (x y : k)
    (hdX : dX.evalEval x y ≠ 0) (hdY : dY.evalEval x y ≠ 0)
    (heq : W.Equation (nX.evalEval x y / dX.evalEval x y) (nY.evalEval x y / dY.evalEval x y)) :
    (clearedPoly W nX dX nY dY).evalEval x y = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  rw [evalEval_clearedPoly]
  have key := clear_denominators W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ (nX.evalEval x y) (dX.evalEval x y) (nY.evalEval x y)
    (dY.evalEval x y) (dX.evalEval x y)⁻¹ (dY.evalEval x y)⁻¹ (inv_mul_cancel₀ hdX) (inv_mul_cancel₀ hdY)
  rw [div_eq_mul_inv, div_eq_mul_inv] at heq
  rw [← key, sub_eq_zero.2 heq, zero_mul]

theorem point_some_ext {W : WeierstrassCurve.Affine k} {x x' y y' : k} (hx : x = x') (hy : y = y')
    {h : W.Nonsingular x y} {h' : W.Nonsingular x' y'} :
    WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some x' y' h' := by
  subst hx; subst hy; rfl

theorem eval₂_polynomial {L : Type*} [CommRing L] (W : WeierstrassCurve.Affine k) (f : k →+* L) (u v : L) :
    W.polynomial.eval₂ (Polynomial.eval₂RingHom f u) v =
      v ^ 2 + (f W.a₁ * u + f W.a₃) * v - (u ^ 3 + f W.a₂ * u ^ 2 + f W.a₄ * u + f W.a₆) := by
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    Polynomial.coe_eval₂RingHom]

end Algebra

section Main

attribute [local instance] MvPolynomial.gradedAlgebra

open WeierstrassCurve.DrinfeldGlobal HomogeneousIdealQuotientGrading

variable {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]

theorem main (X : WeierstrassCurve k) [X.IsElliptic]
    (G : WeierstrassProjModel.RelativeGroupLaw k (π X))
    (ev : SchemeHomOver (t₀ k) (π X) ≃ (X.toProjective.baseChange k).toAffine.Point)
    (hev_add : ∀ P Q : SchemeHomOver (t₀ k) (π X), ev (G.mul (t₀ k) P Q) = ev P + ev Q)
    (hev_chart : ∀ (P : SchemeHomOver (t₀ k) (π X)) (χ : ZChartRing X.toProjective →+* k),
      P.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι X.toProjective →
      ∃ hxy : (X.toProjective.baseChange k).toAffine.Nonsingular (χ (xOverZ X.toProjective)) (χ (yOverZ X.toProjective)),
        ev P = WeierstrassCurve.Affine.Point.some _ _ hxy)
    (α : (X.baseChange k).toAffine.Point →+ (X.baseChange k).toAffine.Point)
    (hα : WeierstrassCurve.IsRationallyRepresented k X X α) :
    ∃ φ : SchemeHomOver (π X) (π X),
      ∀ P : SchemeHomOver (t₀ k) (π X), ev (NeronModelInfra.schemeHomOverComp P φ) = α (ev P) := by
  classical
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ := hα

  have hbc : X.toProjective.baseChange k = X := by
    change X.map (algebraMap k k) = X
    rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]
  have hns : ∀ x y : k, (X.toProjective.baseChange k).toAffine.Nonsingular x y ↔ X.toAffine.Nonsingular x y := by
    intro x y; rw [hbc]
  have heqn : ∀ x y : k, (X.toProjective.baseChange k).toAffine.Equation x y ↔ X.toAffine.Equation x y := by
    intro x y; rw [hbc]
  have hev' : ∀ (p : k[X][Y]) (x y : k), WeierstrassCurve.evalEvalBC k p x y = p.evalEval x y := by
    intro p x y
    simp only [WeierstrassCurve.evalEvalBC, Algebra.algebraMap_self, Polynomial.mapRingHom_id, Polynomial.map_id]

  set W : WeierstrassCurve.Affine k := X.toAffine with hW
  haveI : W.IsElliptic := by rw [hW]; infer_instance
  let A : Type := W.CoordinateRing
  let mkA : k[X][Y] →+* A := WeierstrassCurve.Affine.CoordinateRing.mk W

  have hGA : mkA (clearedPoly W nX dX nY dY) = 0 := by
    apply mk_eq_zero_of_infinite
    have hsub : Bᶜ ⊆ {x : k | ∃ y : k, W.Equation x y ∧ (clearedPoly W nX dX nY dY).evalEval x y = 0} := by
      intro x hx
      obtain ⟨y, hxy⟩ := exists_nonsingular W x
      have hxy' : (X.toProjective.baseChange k).toAffine.Nonsingular x y := (hns x y).2 hxy
      obtain ⟨hdX, hdY, h', -⟩ := hrep x y hxy' hx
      rw [hev'] at hdX hdY
      refine ⟨y, hxy.1, evalEval_clearedPoly_eq_zero W nX dX nY dY x y hdX hdY ?_⟩
      have h1 := h'.1
      rw [heqn, hev', hev', hev', hev'] at h1
      exact h1
    exact (hB.infinite_compl).mono hsub

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∉ B := hB.infinite_compl.nonempty
  obtain ⟨y₀, hx₀y₀⟩ := exists_nonsingular W x₀
  obtain ⟨hdX₀, hdY₀, -⟩ := hrep x₀ y₀ ((hns _ _).2 hx₀y₀) hx₀
  rw [hev'] at hdX₀ hdY₀

  have evalA : ∀ (x y : k), W.Equation x y → ∃ χ : A →+* k, ∀ p, χ (mkA p) = p.evalEval x y :=
    fun x y hxy => ⟨AdjoinRoot.evalEval hxy, fun p => AdjoinRoot.evalEval_mk hxy p⟩
  set sA : A := mkA (dX * dY) with hsA
  have hsA0 : sA ≠ 0 := by
    intro h0
    obtain ⟨χ, hχ⟩ := evalA x₀ y₀ hx₀y₀.1
    have h1 := hχ (dX * dY)
    rw [← hsA, h0, map_zero, evalEval_mul] at h1
    exact mul_ne_zero hdX₀ hdY₀ h1.symm
  let L : Type := Localization.Away sA
  haveI : IsDomain L :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hsA0)
  let ℓ : A →+* L := algebraMap A L
  have hunit : IsUnit (ℓ sA) := IsLocalization.Away.algebraMap_isUnit sA
  have hprod : ℓ (mkA dX) * ℓ (mkA dY) = ℓ sA := by rw [← map_mul, ← map_mul]
  have huX : IsUnit (ℓ (mkA dX)) := isUnit_of_mul_isUnit_left (hprod ▸ hunit)
  have huY : IsUnit (ℓ (mkA dY)) := isUnit_of_mul_isUnit_right (hprod ▸ hunit)
  obtain ⟨iX, hiX⟩ : ∃ iX : L, iX * ℓ (mkA dX) = 1 := ⟨_, huX.val_inv_mul⟩
  obtain ⟨iY, hiY⟩ : ∃ iY : L, iY * ℓ (mkA dY) = 1 := ⟨_, huY.val_inv_mul⟩
  set uL : L := ℓ (mkA nX) * iX with huL
  set vL : L := ℓ (mkA nY) * iY with hvL

  let f : k →+* L := ℓ.comp (mkA.comp ((C : k[X] →+* k[X][Y]).comp C))
  have hf : ∀ a : k, f a = ℓ (mkA (C (C a))) := fun a => rfl
  let i : k[X] →+* L := Polynomial.eval₂RingHom f uL
  have hroot : W.polynomial.eval₂ i vL = 0 := by
    rw [eval₂_polynomial]
    have e2 : ℓ (mkA (clearedPoly W nX dX nY dY)) =
        ℓ (mkA nY) ^ 2 * ℓ (mkA dX) ^ 3 + f W.a₁ * ℓ (mkA nX) * ℓ (mkA nY) * ℓ (mkA dX) ^ 2 * ℓ (mkA dY)
          + f W.a₃ * ℓ (mkA nY) * ℓ (mkA dX) ^ 3 * ℓ (mkA dY)
          - (ℓ (mkA nX) ^ 3 * ℓ (mkA dY) ^ 2 + f W.a₂ * ℓ (mkA nX) ^ 2 * ℓ (mkA dX) * ℓ (mkA dY) ^ 2
            + f W.a₄ * ℓ (mkA nX) * ℓ (mkA dX) ^ 2 * ℓ (mkA dY) ^ 2 + f W.a₆ * ℓ (mkA dX) ^ 3 * ℓ (mkA dY) ^ 2) := by
      simp only [clearedPoly, map_add, map_sub, map_mul, map_pow, hf]
    have e3 := clear_denominators (f W.a₁) (f W.a₂) (f W.a₃) (f W.a₄) (f W.a₆) (ℓ (mkA nX)) (ℓ (mkA dX))
      (ℓ (mkA nY)) (ℓ (mkA dY)) iX iY hiX hiY
    rw [← e2, hGA, map_zero] at e3
    have e4 : (vL ^ 2 + (f W.a₁ * uL + f W.a₃) * vL - (uL ^ 3 + f W.a₂ * uL ^ 2 + f W.a₄ * uL + f W.a₆)) *
        (ℓ (mkA dX) ^ 3 * ℓ (mkA dY) ^ 2) = 0 := by
      rw [huL, hvL]
      linear_combination e3
    exact (IsUnit.mul_left_eq_zero ((huX.pow 3).mul (huY.pow 2))).1 e4
  let σA : A →+* L := AdjoinRoot.lift i vL hroot
  have σA_mkC : ∀ p : k[X], σA (mkA (C p)) = p.eval₂ f uL := fun p => by
    show AdjoinRoot.lift i vL hroot (AdjoinRoot.mk _ (C p)) = _
    rw [AdjoinRoot.lift_mk, eval₂_C]
    rfl
  have σA_x : σA (mkA (C Polynomial.X)) = uL := by rw [σA_mkC, eval₂_X]
  have σA_y : σA (mkA (Y : k[X][Y])) = vL := by
    show AdjoinRoot.lift i vL hroot (AdjoinRoot.mk _ (Y : k[X][Y])) = _
    rw [AdjoinRoot.lift_mk, eval₂_X]
  have σA_CC : ∀ a : k, σA (mkA (C (C a))) = f a := fun a => by rw [σA_mkC, eval₂_C]

  obtain ⟨fZ, hfZ_bij, hfZ_alg, hfZ_gen⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing X.toProjective
  let fA : ZChartRing X.toProjective →+* A := fZ
  let 𝒜 := WeierstrassProjModel.projModelGradingCR X.toProjective
  let ιk : k →+* ZChartRing X.toProjective :=
    (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (coord X.toProjective 2))).comp (algebraMap k (𝒜 0))
  have hfA_ιk : ∀ a : k, fA (ιk a) = mkA (C (C a)) := by
    intro a
    have h := RingHom.congr_fun hfZ_alg a
    refine h.trans ?_
    show algebraMap k A a = mkA (C (C a))
    rw [IsScalarTower.algebraMap_apply k k[X] A, Polynomial.algebraMap_eq, AdjoinRoot.algebraMap_eq]
    exact (AdjoinRoot.mk_C (f := W.polynomial) (C a)).symm
  have chart_over : zChartι X.toProjective ≫ π X = Spec.map (CommRingCat.ofHom ιk) := by
    show Proj.awayι 𝒜 (coord X.toProjective 2) (coord_mem X.toProjective 2) one_pos ≫
      (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (𝒜 0)))) = _
    rw [← Category.assoc, AlgebraicGeometry.Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

  let eZA : ZChartRing X.toProjective ≃+* A := RingEquiv.ofBijective fA hfZ_bij
  let eA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (ZChartRing X.toProjective)) :=
    Spec.map eZA.toCommRingCatIso.hom
  have heA : eA = Spec.map (CommRingCat.ofHom fA) := rfl
  haveI : IsIso eA := inferInstance

  let u : Spec (CommRingCat.of L) ⟶ E X := Spec.map (CommRingCat.ofHom ℓ) ≫ eA ≫ zChartι X.toProjective
  haveI : IsOpenImmersion u := inferInstance
  haveI : Nonempty (Spec (CommRingCat.of L) : Scheme.{0}) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  let φU : Spec (CommRingCat.of L) ⟶ E X := Spec.map (CommRingCat.ofHom σA) ≫ eA ≫ zChartι X.toProjective
  have hℓ_over : ℓ.comp (fA.comp ιk) = f := by
    ext a
    simp only [RingHom.comp_apply, hfA_ιk, hf]
  have hσ_over : σA.comp (fA.comp ιk) = f := by
    ext a
    simp only [RingHom.comp_apply, hfA_ιk, σA_CC]
  have hu_over : u ≫ π X = Spec.map (CommRingCat.ofHom f) := by
    simp only [u, heA, Category.assoc, chart_over]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hℓ_over]
  have hφU_over : φU ≫ π X = Spec.map (CommRingCat.ofHom f) := by
    simp only [φU, heA, Category.assoc, chart_over]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hσ_over]
  obtain ⟨ψ, hψπ, huψ⟩ :=
    AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle (π X) (bundle X G) u φU
      (hφU_over.trans hu_over.symm)
  let Φ : SchemeHomOver (π X) (π X) := ⟨ψ, hψπ⟩

  have hfx : fA (xOverZ X.toProjective) = mkA (C Polynomial.X) := by
    have h := hfZ_gen 1 (MvPolynomial.X 0)
      (by simpa using (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X k 0))
    rw [MvPolynomial.aeval_X] at h
    exact h
  have hfy : fA (yOverZ X.toProjective) = mkA (Y : k[X][Y]) := by
    have h := hfZ_gen 1 (MvPolynomial.X 1)
      (by simpa using (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X k 1))
    rw [MvPolynomial.aeval_X] at h
    exact h

  let Bad : Set k := B ∪ {x | ∃ y, W.Equation x y ∧ (dX * dY).evalEval x y = 0}
  have hBad : Bad.Finite := by
    refine hB.union ?_
    by_contra hinf
    exact hsA0 (mk_eq_zero_of_infinite W (dX * dY) hinf)
  let T : Set (X.toProjective.baseChange k).toAffine.Point :=
    {Q | Q = 0 ∨ ∃ (x y : k) (h : (X.toProjective.baseChange k).toAffine.Nonsingular x y),
      Q = WeierstrassCurve.Affine.Point.some x y h ∧ x ∈ Bad}
  have hT : T.Finite := by
    have hsub : T ⊆ {0} ∪ ⋃ x ∈ Bad, {Q | ∃ (y : k) (h : (X.toProjective.baseChange k).toAffine.Nonsingular x y),
        Q = WeierstrassCurve.Affine.Point.some x y h} := by
      rintro Q (rfl | ⟨x, y, h, rfl, hx⟩)
      · exact Or.inl rfl
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨x, hx, y, h, rfl⟩)
    exact ((Set.finite_singleton _).union
      (hBad.biUnion fun x _ => finite_setOf_point_eq_some (X.toProjective.baseChange k).toAffine x)).subset hsub
  let S : Set (SchemeHomOver (t₀ k) (π X)) := ev ⁻¹' T
  have hS : S.Finite := hT.preimage ev.injective.injOn
  have hgood : ∀ P : SchemeHomOver (t₀ k) (π X), P ∉ S →
      ev (NeronModelInfra.schemeHomOverComp P Φ) = α (ev P) := by
    intro P hP
    have hP' : ev P ∉ T := hP
    rcases hevP : ev P with _ | @⟨x, y, hxy⟩
    · exact (hP' (Or.inl hevP)).elim
    · have hxBad : x ∉ Bad := fun hx => hP' (hevP ▸ Or.inr ⟨x, y, hxy, rfl, hx⟩)
      have hxB : x ∉ B := fun h => hxBad (Or.inl h)
      have hxy' : W.Nonsingular x y := (hns x y).1 hxy
      have hdxy : (dX * dY).evalEval x y ≠ 0 := fun h => hxBad (Or.inr ⟨y, hxy'.1, h⟩)
      have hdXx : dX.evalEval x y ≠ 0 := fun h => hdxy (by rw [evalEval_mul, h, zero_mul])
      have hdYy : dY.evalEval x y ≠ 0 := fun h => hdxy (by rw [evalEval_mul, h, mul_zero])

      let χA : A →+* k := AdjoinRoot.evalEval (p := W.polynomial) hxy'.1
      have hχA : ∀ p, χA (mkA p) = p.evalEval x y := fun p => AdjoinRoot.evalEval_mk hxy'.1 p
      have hχs : IsUnit (χA sA) := by
        rw [hsA, hχA]; exact isUnit_iff_ne_zero.2 hdxy
      let χL : L →+* k := IsLocalization.Away.lift sA hχs
      have hχL : ∀ a : A, χL (ℓ a) = χA a := fun a => IsLocalization.Away.lift_eq sA hχs a
      have hχLiX : χL iX = (dX.evalEval x y)⁻¹ := by
        have h1 : χL iX * dX.evalEval x y = 1 := by
          rw [← hχA, ← hχL, ← map_mul, hiX, map_one]
        exact eq_inv_of_mul_eq_one_left h1
      have hχLiY : χL iY = (dY.evalEval x y)⁻¹ := by
        have h1 : χL iY * dY.evalEval x y = 1 := by
          rw [← hχA, ← hχL, ← map_mul, hiY, map_one]
        exact eq_inv_of_mul_eq_one_left h1

      have hover : (Spec.map (CommRingCat.ofHom (χA.comp fA)) ≫ zChartι X.toProjective) ≫ π X = t₀ k := by
        rw [Category.assoc, chart_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        have : (χA.comp fA).comp ιk = algebraMap k k := by
          ext a
          rw [RingHom.comp_apply, RingHom.comp_apply, hfA_ιk, hχA, evalEval_CC, Algebra.algebraMap_self,
            RingHom.id_apply]
        rw [this]
      have hPfac : P.1 = Spec.map (CommRingCat.ofHom (χA.comp fA)) ≫ zChartι X.toProjective := by
        obtain ⟨hxy'', hevQ⟩ := hev_chart ⟨_, hover⟩ (χA.comp fA) rfl
        have hQP : ev ⟨_, hover⟩ = ev P := by
          rw [hevQ, hevP]
          apply point_some_ext
          · rw [RingHom.comp_apply, hfx, hχA, evalEval_C, eval_X]
          · rw [RingHom.comp_apply, hfy, hχA, evalEval_X]
        have hPQ := ev.injective hQP
        rw [← hPQ]
      have hPu : P.1 = Spec.map (CommRingCat.ofHom χL) ≫ u := by
        rw [hPfac]
        simp only [u, heA, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 3
        ext a
        simp only [RingHom.comp_apply, hχL]
      have hPψ : P.1 ≫ ψ = Spec.map (CommRingCat.ofHom ((χL.comp σA).comp fA)) ≫ zChartι X.toProjective := by
        rw [hPu, Category.assoc, huψ]
        simp only [φU, heA, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      obtain ⟨hns2, hev2⟩ := hev_chart (NeronModelInfra.schemeHomOverComp P Φ) ((χL.comp σA).comp fA) hPψ
      rw [hev2]
      obtain ⟨-, -, h', hα'⟩ := hrep x y hxy hxB
      rw [hα']
      apply point_some_ext
      · rw [hev', hev', RingHom.comp_apply, RingHom.comp_apply, hfx, σA_x, huL, map_mul, hχL, hχA, hχLiX,
          div_eq_mul_inv]
      · rw [hev', hev', RingHom.comp_apply, RingHom.comp_apply, hfy, σA_y, hvL, map_mul, hχL, hχA, hχLiY,
          div_eq_mul_inv]

  exact ⟨Φ, WeierstrassProjModel.apply_schemeHomOverComp_eq_of_finite_of_forall_not_mem X G ev hev_add α Φ S hS hgood⟩

end Main

end P2mExtension
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_schemeHomOver_forall_apply_eq_of_isRationallyRepresented_of_isAlgClosed.P2mExtension"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_schemeHomOver_forall_apply_eq_of_isRationallyRepresented_of_isAlgClosed.P2mExtension"

open P2mExtension in
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
    (hev_chart : ∀ (P : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k)))
        (WeierstrassProjModel.projModelStrCR X.toProjective))
        (χ : WeierstrassCurve.DrinfeldGlobal.ZChartRing X.toProjective →+* k),
      P.1 = Spec.map (CommRingCat.ofHom χ) ≫ WeierstrassCurve.DrinfeldGlobal.zChartι X.toProjective →
      ∃ hxy : (X.toProjective.baseChange k).toAffine.Nonsingular
          (χ (WeierstrassCurve.DrinfeldGlobal.xOverZ X.toProjective))
          (χ (WeierstrassCurve.DrinfeldGlobal.yOverZ X.toProjective)),
        ev P = WeierstrassCurve.Affine.Point.some _ _ hxy)
    (α : (X.baseChange k).toAffine.Point →+ (X.baseChange k).toAffine.Point)
    (hα : WeierstrassCurve.IsRationallyRepresented k X X α) :
    ∃ φ : NeronModelInfra.SchemeHomOver (WeierstrassProjModel.projModelStrCR X.toProjective)
        (WeierstrassProjModel.projModelStrCR X.toProjective),
      ∀ P : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k)))
          (WeierstrassProjModel.projModelStrCR X.toProjective),
        ev (NeronModelInfra.schemeHomOverComp P φ) = α (ev P) :=
  main X G ev hev_add hev_chart α hα

end S_WeierstrassProjModel_exists_schemeHomOver_forall_apply_eq_of_isRationallyRepresented_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassProjModel_exists_schemeHomOver_forall_apply_eq_of_isRationallyRepresented_of_isAlgClosed (solution)
