-- Prove2me | solution 1 for WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/bcaf3518-3dd3-57e4-a7c5-f895b811345a

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul
import Theorems.Thm_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime
import Theorems.Thm_ModularCurve_swapBivar_eq_of_evalSymm
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_eq_all
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq
import Theorems.Thm_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two
import Theorems.Thm_WeierstrassCurve_stepCurve_stepSubgroup_two_eq
import Theorems.Thm_WeierstrassCurve_exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed
import Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j
import Theorems.Thm_WeierstrassCurve_exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2
import Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient2_j
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"

noncomputable section

p2m_open "ModularCurve~dedekindPsi_prime WeierstrassCurve Polynomial"

universe u v

namespace P2MKcKI

section Poly

variable {Ω : Type v} [Field Ω]

abbrev fib (Φ : Polynomial (Polynomial ℤ)) (a : Ω) : Polynomial Ω :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) a)

theorem fib_eq_fibrePoly (Φ : Polynomial (Polynomial ℤ)) (a : Ω) : fib Φ a = fibrePoly Φ a := rfl

theorem monic_fib {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (a : Ω) : (fib data.Φ a).Monic :=
  data.monic.map _

theorem natDegree_fib {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (a : Ω) :
    (fib data.Φ a).natDegree = dedekindPsi N := by
  rw [data.monic.natDegree_map, data.natDegree_eq]

theorem eval_fib_swapBivar (Φ : Polynomial (Polynomial ℤ)) (a b : Ω) :
    (fib (swapBivar Φ) a).eval b = (fib Φ b).eval a := by
  rw [eval_map, eval_map, ← coe_eval₂RingHom, ← coe_eval₂RingHom, swapBivar, ← RingHom.comp_apply]
  congr 1
  refine Polynomial.ringHom_ext' ?_ ?_
  · refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_C, eval₂_X]
    rw [swapInner]
    change eval₂ _ b (aeval (R := ℤ) (X : Polynomial (Polynomial ℤ)) (X : Polynomial ℤ)) = _
    rw [aeval_X, eval₂_X]
  · simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_X, eval₂_C]

theorem eval_fib_symm {ℓ : ℕ} [Fact ℓ.Prime] (data : ModularPolynomialData ℓ) (a b : Ω) :
    (fib data.Φ a).eval b = (fib data.Φ b).eval a := by
  have h := swapBivar_eq_of_evalSymm (data.evalSymm_of_prime ℓ)
  rw [← eval_fib_swapBivar, h]

end Poly

theorem transcendental_of_isRoot_fib (K : Type u) [Field K] {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    [Algebra K Ω] {ℓ : ℕ} [Fact ℓ.Prime] (data : ModularPolynomialData ℓ) {x z : Ω}
    (hx : Transcendental K x) (hz : (fib data.Φ x).IsRoot z) : Transcendental K z := by
  intro hzalg

  set A := algebraicClosure K Ω
  haveI : IsAlgClosed A := IsAlgClosure.isAlgClosed K
  have hzA : z ∈ A := (mem_algebraicClosure_iff).2 hzalg

  have hxroot : (fib data.Φ z).eval x = 0 := by rw [← eval_fib_symm]; exact hz
  set q : Polynomial A := fib data.Φ (⟨z, hzA⟩ : A) with hq
  have hqmap : q.map (algebraMap A Ω) = fib data.Φ z := by
    rw [hq, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_X]
    rfl
  have hqm : q.Monic := monic_fib data _
  have hxq : x ∈ (q.map (algebraMap A Ω)).roots := by
    rw [mem_roots (map_ne_zero hqm.ne_zero), IsRoot.def, hqmap, hxroot]
  rw [(IsAlgClosed.splits q).roots_map (algebraMap A Ω), Multiset.mem_map] at hxq
  obtain ⟨a, -, rfl⟩ := hxq
  exact hx ((mem_algebraicClosure_iff).1 a.2)

section Resultant

variable {Ω : Type v} [Field Ω]

theorem exists_map_eq_prod_fib {ℓ M : ℕ} [NeZero ℓ] [NeZero M] (dℓ : ModularPolynomialData ℓ)
    (dM : ModularPolynomialData M) (dN : ModularPolynomialData (ℓ * M)) (x : Ω)
    {ι : Type*} [Fintype ι] (z : ι → Ω) (hz : fib dℓ.Φ x = ∏ i, (X - C (z i))) :
    ∃ G : Polynomial (Polynomial ℤ), dN.Φ ∣ G ∧
      G.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) x) = ∏ i, fib dM.Φ (z i) := by
  classical
  set B := Polynomial (Polynomial ℤ)
  set f : Polynomial B := dℓ.Φ.map (Polynomial.C : Polynomial ℤ →+* B) with hf
  set g : Polynomial B := dM.Φ.eval₂ (Polynomial.mapRingHom (Int.castRingHom B))
    (Polynomial.C Polynomial.X) with hg
  have hdvd : dN.Φ ∣ f.resultant g := ModularCurve.ModularPolynomialData.dvd_resultant_of_mul ℓ M dℓ dM dN

  set φ₀ : B →+* Polynomial Ω := Polynomial.mapRingHom (Polynomial.eval₂RingHom (Int.castRingHom Ω) x)
    with hφ₀
  obtain ⟨c, hc⟩ := hdvd
  have hev : ∀ zz : Ω, Polynomial.eval (C zz) (g.map φ₀) = fib dM.Φ zz := by
    intro zz
    rw [hg, ← Polynomial.coe_mapRingHom, Polynomial.hom_eval₂, ← Polynomial.coe_evalRingHom,
      Polynomial.hom_eval₂]
    have e1 : (evalRingHom (C zz)).comp ((mapRingHom φ₀).comp (mapRingHom (Int.castRingHom B))) =
        C.comp (eval₂RingHom (Int.castRingHom Ω) zz) :=
      Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp [hφ₀])
    have e2 : (evalRingHom (C zz)) ((mapRingHom φ₀) (C (X : B))) = X := by
      rw [coe_mapRingHom, map_C, coe_evalRingHom, eval_C, hφ₀, coe_mapRingHom, map_X]
    rw [e1, e2]
    rfl
  have key : φ₀ (f.resultant g) = ∏ i, fib dM.Φ (z i) := by
    rw [← Polynomial.resultant_map_map]

    have hf' : f.map φ₀ = (fib dℓ.Φ x).map C := by
      rw [hf, Polynomial.map_map, Polynomial.map_map]
      congr 1
      exact RingHom.ext fun a => by
        rw [RingHom.comp_apply, RingHom.comp_apply, hφ₀, coe_mapRingHom, map_C]
    have hsplit : (f.map φ₀).Splits := by
      rw [hf', hz, Polynomial.map_prod]
      refine Splits.prod fun i _ => ?_
      rw [Polynomial.map_sub, map_X, map_C]
      exact Splits.X_sub_C _
    have hdegf : (f.map φ₀).natDegree = f.natDegree := by
      rw [hf', (monic_fib dℓ x).natDegree_map, natDegree_fib, hf, dℓ.monic.natDegree_map,
        dℓ.natDegree_eq]
    have hlc : (f.map φ₀).leadingCoeff = 1 := by
      rw [hf']; exact (monic_fib dℓ x).map _
    rw [← hdegf, Polynomial.resultant_eq_prod_eval _ _ _ natDegree_map_le hsplit, hlc, one_pow,
      one_mul, hf', hz, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    rw [show (∏ i, (X - C (C (z i) : Polynomial Ω))) =
        ((Finset.univ.val.map fun i => (C (z i) : Polynomial Ω)).map fun a => X - C a).prod by
      rw [Multiset.map_map, Finset.prod_eq_multiset_prod]; rfl,
      roots_multiset_prod_X_sub_C, Multiset.map_map, Finset.prod_eq_multiset_prod]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => hev (z i))
  exact ⟨f.resultant g, ⟨c, hc⟩, key⟩

theorem fib_dvd_prod_fib {ℓ M : ℕ} [NeZero ℓ] [NeZero M] (dℓ : ModularPolynomialData ℓ)
    (dM : ModularPolynomialData M) (dN : ModularPolynomialData (ℓ * M)) (x : Ω)
    {ι : Type*} [Fintype ι] (z : ι → Ω) (hz : fib dℓ.Φ x = ∏ i, (X - C (z i))) :
    fib dN.Φ x ∣ ∏ i, fib dM.Φ (z i) := by
  obtain ⟨G, ⟨c, hc⟩, hG⟩ := exists_map_eq_prod_fib dℓ dM dN x z hz
  refine ⟨c.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) x), ?_⟩
  rw [← hG, hc, Polynomial.map_mul]

end Resultant

theorem dedekindPsi_pos {M : ℕ} (hM : M ≠ 0) : 0 < dedekindPsi M := by
  rw [dedekindPsi]
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨1, ?_, ?_⟩
  · simp [hM]
  · rw [Nat.div_one]; exact Nat.pos_of_ne_zero hM

theorem mul_dedekindPsi_le {ℓ M : ℕ} (hℓ : ℓ ≠ 0) (hM : M ≠ 0) :
    ℓ * dedekindPsi M ≤ dedekindPsi (ℓ * M) := by
  rw [dedekindPsi, dedekindPsi, Finset.mul_sum]
  have hsub : (M.divisors.filter Squarefree) ⊆ ((ℓ * M).divisors.filter Squarefree) := by
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
    exact ⟨⟨hd.1.1.trans (dvd_mul_left M ℓ), mul_ne_zero hℓ hM⟩, hd.2⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _).trans' ?_
  refine Finset.sum_le_sum fun d hd => ?_
  rw [Finset.mem_filter, Nat.mem_divisors] at hd
  rw [Nat.mul_div_assoc ℓ hd.1.1]

theorem dedekindPsi_prime {ℓ : ℕ} (hℓ : ℓ.Prime) : dedekindPsi ℓ = ℓ + 1 := by
  rw [dedekindPsi, hℓ.divisors, Finset.filter_true_of_mem, Finset.sum_pair hℓ.one_lt.ne, Nat.div_one,
    Nat.div_self hℓ.pos]
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · exact squarefree_one
  · exact hℓ.squarefree

section Groups

abbrev CycSub (G : Type*) [AddCommGroup G] (n : ℕ) : Set (AddSubgroup G) :=
  {H | IsAddCyclic H ∧ Nat.card H = n}

theorem finite_of_mem_cycSub {G : Type*} [AddCommGroup G] {n : ℕ} (hn : n ≠ 0) {H : AddSubgroup G}
    (hH : H ∈ CycSub G n) : Finite H :=
  Nat.finite_of_card_ne_zero (hH.2.symm ▸ hn)

theorem natCard_cycSub {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (E : WeierstrassCurve k) [E.IsElliptic] {n : ℕ} [NeZero n] (hn : (n : Ω) ≠ 0) :
    Nat.card (CycSub (E.baseChange Ω).toAffine.Point n) = dedekindPsi n := by
  obtain ⟨e⟩ := E.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := Ω) hn
  have := AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy n e
  rw [← this]
  exact Nat.card_congr (Equiv.refl _)

theorem map_mem_cycSub {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (φ : G →+ G')
    {ℓ M : ℕ} (hℓ : ℓ ≠ 0) {H : AddSubgroup G} (hH : H ∈ CycSub G (ℓ * M))
    (hker : φ.ker ≤ H) (hkercard : Nat.card φ.ker = ℓ) : H.map φ ∈ CycSub G' M := by
  haveI := hH.1
  set ψ : H →+ H.map φ := φ.addSubgroupMap H
  have hψ : Function.Surjective ψ := φ.addSubgroupMap_surjective H
  refine ⟨isAddCyclic_of_surjective ψ hψ, ?_⟩
  have hkerψ : ψ.ker = φ.ker.addSubgroupOf H := by
    ext ⟨h, hh⟩
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, Subtype.ext_iff]
    rfl
  have hcardker : Nat.card ψ.ker = ℓ := by
    rw [hkerψ, Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hker).toEquiv, hkercard]
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv, hcardker, hH.2,
    mul_comm] at h1
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hℓ) h1).symm

theorem comap_map_eq_of_ker_le {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (φ : G →+ G')
    {H : AddSubgroup G} (hker : φ.ker ≤ H) : (H.map φ).comap φ = H :=
  AddSubgroup.comap_map_eq_self hker

theorem eq_of_prime_card {G : Type*} [AddCommGroup G] (H : AddSubgroup G) [IsAddCyclic H] [Finite H]
    {ℓ : ℕ} (hℓ : ℓ.Prime) {C C' : AddSubgroup G} (hC : C ≤ H) (hC' : C' ≤ H)
    (hcard : Nat.card C = ℓ) (hcard' : Nat.card C' = ℓ) : C = C' := by
  classical
  haveI : Fintype H := Fintype.ofFinite H

  set T : Finset H := Finset.univ.filter fun a : H => ℓ • a = 0 with hT
  have hTle : T.card ≤ ℓ := IsAddCyclic.card_nsmul_eq_zero_le hℓ.pos
  have key : ∀ {D : AddSubgroup G}, D ≤ H → Nat.card D = ℓ →
      (D.addSubgroupOf H : Set H).toFinset = T := by
    intro D hD hDcard
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      rw [Set.mem_toFinset, SetLike.mem_coe, AddSubgroup.mem_addSubgroupOf] at ha
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      apply Subtype.ext
      rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
      have := card_nsmul_eq_zero' (G := D) (x := ⟨(a : G), ha⟩)
      rw [hDcard] at this
      exact congrArg Subtype.val this
    · rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
      change T.card ≤ Nat.card (D.addSubgroupOf H)
      rw [Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hD).toEquiv, hDcard]
      exact hTle
  have h := (key hC hcard).trans (key hC' hcard').symm
  have h' : C.addSubgroupOf H = C'.addSubgroupOf H := by
    ext a
    have := congrArg (fun s : Finset H => a ∈ s) h
    simpa only [Set.mem_toFinset, SetLike.mem_coe, eq_iff_iff] using this
  have h2 := (AddSubgroup.addSubgroupOf_inj).1 h'
  rwa [inf_eq_left.2 hC, inf_eq_left.2 hC'] at h2

end Groups

theorem exists_algEquiv_apply_eq {F : Type u} [Field F] {Ω : Type v} [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {p : Polynomial F} (hirr : Irreducible p) {r r' : Ω}
    (hr : (p.map (algebraMap F Ω)).IsRoot r) (hr' : (p.map (algebraMap F Ω)).IsRoot r') :
    ∃ τ : Ω ≃ₐ[F] Ω, τ r = r' := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Normal F Ω := ⟨fun x => IsAlgClosed.splits _⟩
  have hp0 : p ≠ 0 := hirr.ne_zero
  have hint : IsIntegral F r := Algebra.IsIntegral.isIntegral r

  have haeval : aeval r p = 0 := by rwa [IsRoot.def, eval_map, ← aeval_def] at hr
  have hmin : minpoly F r ∣ p := minpoly.dvd F r haeval
  have hassoc : p ∣ minpoly F r * C p.leadingCoeff := by
    obtain ⟨q, hq⟩ := hmin
    have hq' : IsUnit q := by
      rcases hirr.isUnit_or_isUnit hq with h | h
      · exact absurd h (minpoly.not_isUnit F r)
      · exact h
    obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.1 hq'
    refine ⟨C c⁻¹ * C p.leadingCoeff, ?_⟩
    rw [hq]
    have hc0 : c ≠ 0 := hc.ne_zero
    rw [mul_assoc, ← mul_assoc (C c), ← C_mul, mul_inv_cancel₀ hc0, C_1, one_mul]
  have hr'min : aeval r' (minpoly F r) = 0 := by
    have h1 : aeval r' p = 0 := by rwa [IsRoot.def, eval_map, ← aeval_def] at hr'
    obtain ⟨q, hq⟩ := hassoc
    have h2 : aeval r' (minpoly F r * C p.leadingCoeff) = 0 := by rw [hq, map_mul, h1, zero_mul]
    rw [map_mul, aeval_C, mul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact h2
    · exact absurd ((map_eq_zero _).1 h2) (leadingCoeff_ne_zero.2 hp0)
  have hβ' : r' ∈ ((minpoly F r).map (algebraMap F Ω)).roots := by
    rw [mem_roots (map_ne_zero (minpoly.ne_zero hint)), IsRoot.def, eval_map, ← aeval_def]
    exact hr'min
  let f₀ : IntermediateField.adjoin F {r} →ₐ[F] Ω :=
    (IntermediateField.algHomAdjoinIntegralEquiv F hint).symm ⟨r', hβ'⟩
  have hf₀ : f₀ (IntermediateField.AdjoinSimple.gen F r) = r' :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen F hint _
  let f₁ : Ω →ₐ[F] Ω := f₀.liftNormal Ω
  refine ⟨AlgEquiv.ofBijective f₁ (Algebra.IsAlgebraic.algHom_bijective f₁), ?_⟩
  change f₁ r = r'
  have := AlgHom.liftNormal_commutes f₀ Ω (IntermediateField.AdjoinSimple.gen F r)
  rw [IntermediateField.AdjoinSimple.algebraMap_gen] at this
  change f₁ r = algebraMap Ω Ω (f₀ _) at this
  rw [this, hf₀]; rfl

section Pkg

variable {Ω : Type v} [Field Ω] [DecidableEq Ω]

structure StepPkg (E : WeierstrassCurve Ω) [E.IsElliptic] (ℓ : ℕ) [NeZero ℓ] (dℓ : ModularPolynomialData ℓ) where
  ι : Type
  fι : Fintype ι
  card_ι : Fintype.card ι = ℓ + 1
  W : ι → WeierstrassCurve Ω
  hW : ∀ i, (W i).IsElliptic
  φ : ∀ i, E.toAffine.Point →+ (W i).toAffine.Point
  ker_card : ∀ i, Nat.card (φ i).ker = ℓ
  ker_inj : ∀ i i', (φ i).ker = (φ i').ker → i = i'
  prod : fib dℓ.Φ E.j = ∏ i, (X - C (@WeierstrassCurve.j Ω _ (W i) (hW i)))
  bridge : ∀ (H : AddSubgroup E.toAffine.Point) [IsAddCyclic H] [Finite H] (i : ι), (φ i).ker ≤ H →
    (⟨E.stepCurve H ℓ, E.stepSubgroup H ℓ⟩ : Σ V : WeierstrassCurve Ω, AddSubgroup V.toAffine.Point) =
      ⟨W i, H.map (φ i)⟩

attribute [scoped instance] StepPkg.fι

theorem nonempty_stepPkg_odd [IsAlgClosed Ω] (E : WeierstrassCurve Ω) [E.IsElliptic]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓΩ : (ℓ : Ω) ≠ 0) (dℓ : ModularPolynomialData ℓ) :
    Nonempty (StepPkg E ℓ dℓ) := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨ι, _, hι, Q, hQ, hQinj, hΔ⟩ :=
    E.exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero (ℓ := ℓ) hℓ2 hℓΩ

  have hφex := fun i => E.exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed hℓ hℓ2 hℓΩ (Q i) (hQ i)
  choose φ hφker hφ using hφex
  refine ⟨{
    ι := ι
    fι := inferInstance
    card_ι := hι
    W := fun i => E.veluQuotient (E.oddOrderSummingSet (Q i) (ℓ / 2))
    hW := fun i => ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩
    φ := φ
    ker_card := fun i => by rw [hφker i, Nat.card_zmultiples, hQ i]
    ker_inj := fun i i' h => hQinj (by simpa only [hφker] using h)
    prod := ?_
    bridge := ?_ }⟩
  · exact ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j hℓ2 hℓΩ dℓ E hι Q hQ
      hQinj hΔ
  · intro H _ _ i hi
    have hQH : Q i ∈ H := hi (by rw [hφker i]; exact AddSubgroup.mem_zmultiples _)
    exact E.stepCurve_stepSubgroup_eq_of_prime_ne_two hℓ hℓ2 H (Q i) hQH (hQ i) (φ i) (hφker i) (hφ i)

theorem mem_ker_veluPointMap2 (E : WeierstrassCurve Ω) [E.IsElliptic] (h2 : (2 : Ω) ≠ 0) {x₀ y₀ : Ω}
    (hQ : E.toAffine.Equation x₀ y₀) (hgy : E.veluGy x₀ y₀ = 0) (hΔ : (E.veluQuotient2 x₀ y₀).Δ ≠ 0)
    (φ : E.toAffine.Point →+ (E.veluQuotient2 x₀ y₀).toAffine.Point)
    (hφ : ⇑φ = veluPointMap2 h2 hQ hgy hΔ) (P : E.toAffine.Point) :
    P ∈ φ.ker ↔ P = 0 ∨ P = .some x₀ y₀ ((E.toAffine.equation_iff_nonsingular).1 hQ) := by
  rw [AddMonoidHom.mem_ker, hφ]
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  · by_cases hx : x = x₀
    · rw [veluPointMap2_some_of_eq _ _ _ _ _ hx]
      refine ⟨fun _ => ?_, fun _ => rfl⟩
      right
      subst hx
      have hneg : E.toAffine.negY x y₀ = y₀ := by
        rw [Affine.negY]; rw [veluGy] at hgy; linear_combination hgy
      rcases Affine.Y_eq_of_X_eq h.1 hQ rfl with hy | hy
      · subst hy; rfl
      · rw [hneg] at hy; subst hy; rfl
    · rw [veluPointMap2_some_of_ne _ _ _ _ _ hx]
      constructor
      · intro h0; exact absurd h0 (Affine.Point.some_ne_zero _)
      · rintro (h0 | hP)
        · exact absurd h0 (Affine.Point.some_ne_zero _)
        · exact absurd (Affine.Point.some.inj hP).1 hx

theorem nonempty_stepPkg_two [IsAlgClosed Ω] (E : WeierstrassCurve Ω) [E.IsElliptic]
    (h2 : (2 : Ω) ≠ 0) (d2 : ModularPolynomialData 2) : Nonempty (StepPkg E 2 d2) := by
  obtain ⟨ι, _, hι, P, hPinj, hPeq, hPgy, hΔ⟩ :=
    E.exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero h2
  have hφex := fun i => E.exists_addMonoidHom_coe_eq_veluPointMap2 h2 (hPeq i) (hPgy i) (hΔ i)
  choose φ hφ using hφex
  have hns : ∀ i, E.toAffine.Nonsingular (P i).1 (P i).2 := fun i =>
    (E.toAffine.equation_iff_nonsingular).1 (hPeq i)

  have hker : ∀ i, (φ i).ker = AddSubgroup.zmultiples (.some (P i).1 (P i).2 (hns i)) := by
    intro i
    ext Q
    rw [mem_ker_veluPointMap2 E h2 (hPeq i) (hPgy i) (hΔ i) (φ i) (hφ i)]

    have h2Q : (2 : ℕ) • (Affine.Point.some (P i).1 (P i).2 (hns i) : E.toAffine.Point) = 0 := by
      rw [two_nsmul, ← eq_neg_iff_add_eq_zero, Affine.Point.neg_some]
      congr 1
      rw [Affine.negY]; have := hPgy i; rw [veluGy] at this; linear_combination -this
    have hord : addOrderOf (Affine.Point.some (P i).1 (P i).2 (hns i) : E.toAffine.Point) = 2 :=
      addOrderOf_eq_prime_iff.2 ⟨h2Q, Affine.Point.some_ne_zero _⟩
    constructor
    · rintro (rfl | rfl)
      · exact AddSubgroup.zero_mem _
      · exact AddSubgroup.mem_zmultiples _
    · intro hQ
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hQ
      have hk : (k % 2) • (Affine.Point.some (P i).1 (P i).2 (hns i) : E.toAffine.Point) =
          k • Affine.Point.some (P i).1 (P i).2 (hns i) := by
        have := mod_addOrderOf_zsmul (Affine.Point.some (P i).1 (P i).2 (hns i) : E.toAffine.Point) k
        rwa [hord, Nat.cast_ofNat] at this
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left; rw [← hk, h, zero_smul]
      · right; rw [← hk, h, one_smul]
  refine ⟨{
    ι := ι
    fι := inferInstance
    card_ι := hι
    W := fun i => E.veluQuotient2 (P i).1 (P i).2
    hW := fun i => ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩
    φ := φ
    ker_card := fun i => by
      rw [hker i, Nat.card_zmultiples]
      exact addOrderOf_eq_prime_iff.2 ⟨by
        rw [two_nsmul, ← eq_neg_iff_add_eq_zero, Affine.Point.neg_some]
        congr 1
        rw [Affine.negY]; have := hPgy i; rw [veluGy] at this; linear_combination -this,
        Affine.Point.some_ne_zero _⟩
    ker_inj := ?_
    prod := ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient2_j h2 d2 E hι P hPinj
      hPeq hPgy hΔ
    bridge := ?_ }⟩
  · intro i i' h
    apply hPinj
    have hmem : (Affine.Point.some (P i).1 (P i).2 (hns i) : E.toAffine.Point) ∈ (φ i').ker := by
      rw [← h, hker i]; exact AddSubgroup.mem_zmultiples _
    rw [mem_ker_veluPointMap2 E h2 (hPeq i') (hPgy i') (hΔ i') (φ i') (hφ i')] at hmem
    rcases hmem with h0 | hP
    · exact absurd h0 (Affine.Point.some_ne_zero _)
    · exact Prod.ext (Affine.Point.some.inj hP).1 (Affine.Point.some.inj hP).2
  · intro H _ _ i hi
    have hQH : (Affine.Point.some (P i).1 (P i).2 (hns i) : E.toAffine.Point) ∈ H :=
      hi (by rw [hker i]; exact AddSubgroup.mem_zmultiples _)
    exact E.stepCurve_stepSubgroup_two_eq h2 H (hns i) hQH (hPgy i) (hΔ i) (φ i) (hφ i)

theorem nonempty_stepPkg [IsAlgClosed Ω] (E : WeierstrassCurve Ω) [E.IsElliptic]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓΩ : (ℓ : Ω) ≠ 0) (dℓ : ModularPolynomialData ℓ) :
    Nonempty (StepPkg E ℓ dℓ) := by
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    exact nonempty_stepPkg_two E (by exact_mod_cast hℓΩ) dℓ
  · exact nonempty_stepPkg_odd E hℓ2 hℓΩ dℓ

end Pkg

theorem separable_fib (K : Type u) [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
    {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (hNK : (N : K) ≠ 0)
    (x : Ω) (hx : Transcendental K x) : (fib data.Φ x).Separable := by
  set φ : Polynomial K →+* Ω := (Polynomial.aeval (R := K) x).toRingHom with hφ
  have hφinj : Function.Injective φ := transcendental_iff_injective.1 hx
  have hφ0 : nonZeroDivisors (Polynomial K) ≤ (nonZeroDivisors Ω).comap φ := fun p hp =>
    mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero hp (hφinj (h.trans (map_zero φ).symm)))
  set ψ : RatFunc K →+* Ω := RatFunc.liftRingHom φ hφ0
  have hsep := (data.separable_map_ratFunc_of_natCast_ne_zero K N hNK).map (f := ψ)
  rw [Polynomial.map_map, Polynomial.map_map] at hsep
  convert hsep using 2 <;> first | (with_reducible_and_instances rfl) | rfl | skip
  refine Polynomial.ringHom_ext ?_ ?_
  · intro n
    simp [ψ, φ]
  · rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      Polynomial.coe_mapRingHom, Polynomial.map_X]
    change x = ψ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
    rw [RatFunc.liftRingHom_algebraMap]
    simp [φ]

theorem card_roots_fib (K : Type u) [Field K] {Ω : Type v} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [DecidableEq Ω] {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (hNK : (N : K) ≠ 0)
    (x : Ω) (hx : Transcendental K x) : (fib data.Φ x).roots.toFinset.card = dedekindPsi N := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots (separable_fib K data hNK x hx)),
    ← natDegree_fib data x]
  exact (Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _))

theorem cyclicQuotientJ_congr {Ω : Type v} [Field Ω] [DecidableEq Ω] {V V' : WeierstrassCurve Ω}
    {H : AddSubgroup V.toAffine.Point} {H' : AddSubgroup V'.toAffine.Point}
    (h : (⟨V, H⟩ : Σ V : WeierstrassCurve Ω, AddSubgroup V.toAffine.Point) = ⟨V', H'⟩) (n : ℕ) :
    V.cyclicQuotientJ H n = V'.cyclicQuotientJ H' n := by
  cases h; rfl

section Core

variable (K : Type u) [Field K] {F : Type u} [Field F]
  {Ω : Type v} [Field Ω] [DecidableEq Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Algebra K Ω]

theorem bijOn_core {ℓ M : ℕ} [Fact ℓ.Prime] [NeZero M] (hMK : ((ℓ * M : ℕ) : K) ≠ 0)
    (dℓ : ModularPolynomialData ℓ) (dM : ModularPolynomialData M) (dN : ModularPolynomialData (ℓ * M))
    (hmin : (ℓ * M).minFac = ℓ)
    (E₀ : WeierstrassCurve F) [E₀.IsElliptic] (hx : Transcendental K (algebraMap F Ω E₀.j))
    (pF : Polynomial F) (hpF : pF.map (algebraMap F Ω) = fib dN.Φ (algebraMap F Ω E₀.j))
    (hirr : Irreducible pF)
    (IH : ∀ (W : WeierstrassCurve Ω) [W.IsElliptic], Transcendental K W.j →
      Set.BijOn (fun C : AddSubgroup W.toAffine.Point => W.cyclicQuotientJ C M)
        (CycSub W.toAffine.Point M) {y | (fib dM.Φ W.j).IsRoot y}) :
    Set.BijOn (fun H : AddSubgroup (E₀.baseChange Ω).toAffine.Point =>
        (E₀.baseChange Ω).cyclicQuotientJ H (ℓ * M))
      (CycSub (E₀.baseChange Ω).toAffine.Point (ℓ * M)) {y | (fib dN.Φ (algebraMap F Ω E₀.j)).IsRoot y} := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI hEell : (E₀.baseChange Ω).IsElliptic := show (E₀.map _).IsElliptic from inferInstance
  have hℓ : ℓ.Prime := Fact.out
  set E := E₀.baseChange Ω with hE
  set N := ℓ * M with hN
  set x : Ω := algebraMap F Ω E₀.j with hxF
  have hxdef : x = E.j := by
    rw [hxF]; change _ = (E₀.map (algebraMap F Ω)).j; exact (E₀.map_j _).symm
  have hxT : Transcendental K x := hx

  have hNK : (N : K) ≠ 0 := hMK
  have hNΩ : (N : Ω) ≠ 0 := fun h => hNK (by
    apply (algebraMap K Ω).injective; rw [map_natCast, h, map_zero])
  have hℓΩ : (ℓ : Ω) ≠ 0 := fun h => hNΩ (by rw [hN, Nat.cast_mul, h, zero_mul])
  have hMΩ : (M : Ω) ≠ 0 := fun h => hNΩ (by rw [hN, Nat.cast_mul, h, mul_zero])
  have hℓK : (ℓ : K) ≠ 0 := fun h => hNK (by rw [hN, Nat.cast_mul, h, zero_mul])
  have hMK' : (M : K) ≠ 0 := fun h => hNK (by rw [hN, Nat.cast_mul, h, mul_zero])
  have hM0 : M ≠ 0 := NeZero.ne M
  have hN2 : 2 ≤ N := by
    have := hℓ.two_le; have := Nat.pos_of_ne_zero hM0; nlinarith
  haveI : NeZero N := ⟨by omega⟩

  obtain ⟨pkg⟩ := nonempty_stepPkg E hℓΩ dℓ
  let z : pkg.ι → Ω := fun i => @WeierstrassCurve.j Ω _ (pkg.W i) (pkg.hW i)
  have hprod : fib dℓ.Φ x = ∏ i, (X - C (z i)) := hxdef ▸ pkg.prod
  have hz : ∀ i, (fib dℓ.Φ x).IsRoot (z i) := fun i => by
    rw [hprod, IsRoot.def, eval_prod, Finset.prod_eq_zero_iff]
    exact ⟨i, Finset.mem_univ _, by simp⟩
  have hzT : ∀ i, Transcendental K (z i) := fun i => transcendental_of_isRoot_fib K dℓ hxT (hz i)
  have IHi : ∀ i, Set.BijOn (fun C : AddSubgroup (pkg.W i).toAffine.Point => (pkg.W i).cyclicQuotientJ C M)
      (CycSub (pkg.W i).toAffine.Point M) {y | (fib dM.Φ (z i)).IsRoot y} :=
    fun i => @IH (pkg.W i) (pkg.hW i) (hzT i)

  set Q : Polynomial Ω := ∏ i, fib dM.Φ (z i) with hQ
  have hQm : Q.Monic := monic_prod_of_monic _ _ fun i _ => monic_fib dM (z i)
  have hQ0 : Q ≠ 0 := hQm.ne_zero
  have hpQ : fib dN.Φ x ∣ Q := fib_dvd_prod_fib dℓ dM dN x z hprod
  have hQdeg : Q.natDegree = Fintype.card pkg.ι * dedekindPsi M := by
    rw [hQ, natDegree_prod_of_monic _ _ fun i _ => monic_fib dM (z i)]
    simp only [natDegree_fib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hQroots : Q.roots.card = (ℓ + 1) * dedekindPsi M := by
    rw [← pkg.card_ι, ← hQdeg]; exact Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _)
  set R : Finset Ω := (fib dN.Φ x).roots.toFinset with hR
  have hRcard : R.card = dedekindPsi N := card_roots_fib K dN hNK x hxT
  have hmemR : ∀ y, y ∈ R ↔ (fib dN.Φ x).IsRoot y := fun y => by
    rw [hR, Multiset.mem_toFinset, mem_roots (monic_fib dN x).ne_zero]

  have hTFcard' : Nat.card (CycSub E.toAffine.Point N) = dedekindPsi N := natCard_cycSub E₀ hNΩ
  have hTF : (CycSub E.toAffine.Point N).Finite := by
    rw [← Set.finite_coe_iff]
    exact Nat.finite_of_card_ne_zero (by rw [hTFcard']; exact (dedekindPsi_pos (NeZero.ne N)).ne')
  set TF := hTF.toFinset with hTFdef
  have hmemTF : ∀ H, H ∈ TF ↔ H ∈ CycSub E.toAffine.Point N := fun H => Set.Finite.mem_toFinset _
  have hTFcard : TF.card = dedekindPsi N := by
    rw [hTFdef, ← Set.ncard_eq_toFinset_card _ hTF, ← Nat.card_coe_set_eq, hTFcard']

  have hkerCyc : ∀ i, (pkg.φ i).ker ∈ CycSub E.toAffine.Point ℓ := fun i =>
    ⟨isAddCyclic_of_prime_card (pkg.ker_card i), pkg.ker_card i⟩
  have hexists_i : ∀ H, H ∈ CycSub E.toAffine.Point N → ∃ i, (pkg.φ i).ker ≤ H := by
    intro H hH
    haveI := hH.1
    haveI : Finite H := finite_of_mem_cycSub (NeZero.ne N) hH
    haveI : Fintype H := Fintype.ofFinite H

    have hdvd : ℓ ∣ Fintype.card H := by
      rw [Fintype.card_eq_nat_card, hH.2, hN]; exact dvd_mul_right ℓ M
    obtain ⟨⟨q, hqH⟩, hq⟩ := exists_prime_addOrderOf_dvd_card ℓ hdvd
    have hq' : addOrderOf q = ℓ := by
      rw [← hq]; exact addOrderOf_injective H.subtype Subtype.coe_injective ⟨q, hqH⟩
    set D := AddSubgroup.zmultiples q with hD
    have hDcyc : D ∈ CycSub E.toAffine.Point ℓ :=
      ⟨inferInstance, by rw [hD, Nat.card_zmultiples, hq']⟩
    have hDH : D ≤ H := AddSubgroup.zmultiples_le.2 hqH

    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓcard : Nat.card (CycSub E.toAffine.Point ℓ) = ℓ + 1 := by
      rw [natCard_cycSub E₀ hℓΩ]; exact dedekindPsi_prime hℓ
    let kerMap : pkg.ι → CycSub E.toAffine.Point ℓ := fun i => ⟨(pkg.φ i).ker, hkerCyc i⟩
    have hinj : Function.Injective kerMap := fun i i' h => pkg.ker_inj i i' (congrArg Subtype.val h)
    haveI : Finite (CycSub E.toAffine.Point ℓ) := Nat.finite_of_card_ne_zero (by rw [hℓcard]; omega)
    have hbij := hinj.bijective_of_nat_card_le (by rw [hℓcard, Nat.card_eq_fintype_card, pkg.card_ι])
    obtain ⟨i, hi⟩ := hbij.2 ⟨D, hDcyc⟩
    exact ⟨i, (congrArg Subtype.val hi).le.trans hDH⟩
  have hunique_i : ∀ H, H ∈ CycSub E.toAffine.Point N → ∀ i i',
      (pkg.φ i).ker ≤ H → (pkg.φ i').ker ≤ H → i = i' := by
    intro H hH i i' hi hi'
    haveI := hH.1
    haveI : Finite H := finite_of_mem_cycSub (NeZero.ne N) hH
    exact pkg.ker_inj i i' (eq_of_prime_card H hℓ hi hi' (pkg.ker_card i) (pkg.ker_card i'))

  have hval : ∀ H, H ∈ CycSub E.toAffine.Point N → ∀ i, (pkg.φ i).ker ≤ H →
      E.cyclicQuotientJ H N = (pkg.W i).cyclicQuotientJ (H.map (pkg.φ i)) M := by
    intro H hH i hi
    haveI := hH.1
    haveI : Finite H := finite_of_mem_cycSub (NeZero.ne N) hH
    rw [cyclicQuotientJ_eq_of_two_le E H hN2, hmin,
      show N / ℓ = M from by rw [hN]; exact Nat.mul_div_cancel_left M hℓ.pos]
    exact cyclicQuotientJ_congr (pkg.bridge H i hi) M
  have hmapCyc : ∀ H, H ∈ CycSub E.toAffine.Point N → ∀ i, (pkg.φ i).ker ≤ H →
      H.map (pkg.φ i) ∈ CycSub (pkg.W i).toAffine.Point M := fun H hH i hi =>
    map_mem_cycSub (pkg.φ i) hℓ.ne_zero hH hi (pkg.ker_card i)
  have hvalroot : ∀ H, H ∈ CycSub E.toAffine.Point N → ∀ i, (pkg.φ i).ker ≤ H →
      (fib dM.Φ (z i)).IsRoot (E.cyclicQuotientJ H N) := by
    intro H hH i hi
    rw [hval H hH i hi]
    exact (IHi i).mapsTo (hmapCyc H hH i hi)

  set Y : Finset Ω := Q.roots.toFinset with hY
  have hmemY : ∀ y, y ∈ Y ↔ Q.IsRoot y := fun y => by rw [hY, Multiset.mem_toFinset, mem_roots hQ0]
  have hrootQ : ∀ y i, (fib dM.Φ (z i)).IsRoot y → Q.IsRoot y := fun y i h => by
    rw [IsRoot.def, hQ, eval_prod, Finset.prod_eq_zero_iff]
    exact ⟨i, Finset.mem_univ _, h⟩
  have hvalY : ∀ H, H ∈ CycSub E.toAffine.Point N → E.cyclicQuotientJ H N ∈ Y := by
    intro H hH
    obtain ⟨i, hi⟩ := hexists_i H hH
    exact (hmemY _).2 (hrootQ _ i (hvalroot H hH i hi))
  have hRY : R ⊆ Y := fun y hy => by
    rw [hmemY]
    obtain ⟨c, hc⟩ := hpQ
    rw [IsRoot.def, hc, eval_mul, ((hmemR y).1 hy).eq_zero, zero_mul]

  let t : Ω → ℕ := fun y => (TF.filter fun H => E.cyclicQuotientJ H N = y).card
  let sc : Ω → ℕ := fun y => Q.roots.count y

  have hιne : Nonempty pkg.ι := Fintype.card_pos_iff.1 (by rw [pkg.card_ι]; omega)
  let iOf : AddSubgroup E.toAffine.Point → pkg.ι := fun H =>
    if h : ∃ i, (pkg.φ i).ker ≤ H then h.choose else hιne.some
  have hiOf : ∀ H, H ∈ CycSub E.toAffine.Point N → (pkg.φ (iOf H)).ker ≤ H := by
    intro H hH
    have h := hexists_i H hH
    have : iOf H = h.choose := dif_pos h
    rw [this]
    exact h.choose_spec
  have ht_le : ∀ y, t y ≤ sc y := by
    intro y
    refine le_trans (Finset.card_le_card_of_injOn iOf (t := Finset.univ.filter fun i =>
      (fib dM.Φ (z i)).IsRoot y) ?_ ?_) ?_
    · intro H hH
      rw [Finset.coe_filter, Set.mem_setOf_eq, hmemTF] at hH
      rw [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨Finset.mem_univ _, hH.2 ▸ hvalroot H hH.1 _ (hiOf H hH.1)⟩
    · intro H hH H' hH' hii
      rw [Finset.coe_filter, Set.mem_setOf_eq, hmemTF] at hH hH'
      have hi := hiOf H hH.1
      have hi' := hiOf H' hH'.1
      rw [← hii] at hi'
      have hveq : (pkg.W (iOf H)).cyclicQuotientJ (H.map (pkg.φ (iOf H))) M =
          (pkg.W (iOf H)).cyclicQuotientJ (H'.map (pkg.φ (iOf H))) M := by
        rw [← hval H hH.1 _ hi, ← hval H' hH'.1 _ hi', hH.2, hH'.2]
      have hmapeq := (IHi (iOf H)).injOn (hmapCyc H hH.1 _ hi) (hmapCyc H' hH'.1 _ hi') hveq
      rw [← comap_map_eq_of_ker_le _ hi, ← comap_map_eq_of_ker_le _ hi', hmapeq]
    ·
      change _ ≤ Q.roots.count y
      rw [hQ, Polynomial.roots_prod _ _ (by rw [← hQ]; exact hQ0), Multiset.count_bind, Finset.card_filter,
        ← Finset.sum_eq_multiset_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      split_ifs with h
      · rw [count_roots]
        exact (Polynomial.rootMultiplicity_pos (monic_fib dM (z i)).ne_zero).2 h
      · exact Nat.zero_le _

  have hτval : ∀ (τ : Ω ≃ₐ[F] Ω) (H : AddSubgroup E.toAffine.Point),
      E.cyclicQuotientJ (H.map (WeierstrassCurve.Affine.Point.map (τ : Ω →ₐ[F] Ω))) N =
        τ (E.cyclicQuotientJ H N) := fun τ H =>
    WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed E₀ (τ : Ω →ₐ[F] Ω) H N
  have hτCyc : ∀ (τ : Ω ≃ₐ[F] Ω) H, H ∈ CycSub E.toAffine.Point N →
      H.map (WeierstrassCurve.Affine.Point.map (τ : Ω →ₐ[F] Ω)) ∈ CycSub E.toAffine.Point N := by
    intro τ H hH
    haveI := hH.1
    let e := H.equivMapOfInjective _ (WeierstrassCurve.Affine.Point.map_injective (τ : Ω →ₐ[F] Ω))
    exact ⟨isAddCyclic_of_surjective e e.surjective, by rw [← hH.2]; exact (Nat.card_congr e.toEquiv).symm⟩
  have hτt_le : ∀ (τ : Ω ≃ₐ[F] Ω) y, t y ≤ t (τ y) := by
    intro τ y
    refine Finset.card_le_card_of_injOn (fun H => H.map (WeierstrassCurve.Affine.Point.map (τ : Ω →ₐ[F] Ω)))
      ?_ ?_
    · intro H hH
      rw [Finset.coe_filter, Set.mem_setOf_eq, hmemTF] at hH ⊢
      exact ⟨hτCyc τ H hH.1, by rw [hτval, hH.2]⟩
    · intro H _ H' _ h
      exact AddSubgroup.map_injective (WeierstrassCurve.Affine.Point.map_injective _) h
  have hτt : ∀ (τ : Ω ≃ₐ[F] Ω) y, t (τ y) = t y := by
    intro τ y
    refine le_antisymm ?_ (hτt_le τ y)
    have := hτt_le τ.symm (τ y)
    rwa [AlgEquiv.symm_apply_apply] at this
  have hτR : ∀ r ∈ R, ∀ r' ∈ R, ∃ τ : Ω ≃ₐ[F] Ω, τ r = r' := by
    intro r hr r' hr'
    have hpF' : pF.map (algebraMap F Ω) = fib dN.Φ x := hpF
    rw [hmemR, ← hpF'] at hr hr'
    exact exists_algEquiv_apply_eq hirr hr hr'
  have hτs : ∀ (τ : Ω ≃ₐ[F] Ω) y, sc (τ y) = sc y := by
    intro τ y
    obtain ⟨G, -, hG⟩ := exists_map_eq_prod_fib dℓ dM dN x z hprod
    have hfix : (τ : Ω →+* Ω).comp (Polynomial.eval₂RingHom (Int.castRingHom Ω) x) =
        Polynomial.eval₂RingHom (Int.castRingHom Ω) x := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_X, RingHom.coe_coe]
      exact τ.commutes _
    have hQτ : Q.map (τ : Ω →+* Ω) = Q := by rw [hQ, ← hG, Polynomial.map_map, hfix]
    have hrootsτ : Q.roots.map (τ : Ω →+* Ω) = Q.roots := by
      rw [Polynomial.roots_map_of_injective_of_card_eq_natDegree (τ : Ω →+* Ω).injective
        (Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits Q)), hQτ]
    change Q.roots.count (τ y) = Q.roots.count y
    conv_lhs => rw [← hrootsτ]
    exact Multiset.count_map_eq_count' _ _ (τ : Ω →+* Ω).injective y

  have hsum_t : ∑ y ∈ Y, t y = dedekindPsi N := by
    rw [← hTFcard]
    exact (Finset.card_eq_sum_card_fiberwise fun H hH => by
      exact hvalY H ((hmemTF H).1 hH)).symm
  have hsum_s : ∑ y ∈ Y, sc y = (ℓ + 1) * dedekindPsi M := by
    rw [← hQroots]; exact Multiset.toFinset_sum_count_eq _
  have hsR : ∀ r ∈ R, 1 ≤ sc r := by
    intro r hr
    change 1 ≤ Q.roots.count r
    rw [count_roots]
    exact (Polynomial.rootMultiplicity_pos hQ0).2 ((hmemY r).1 (hRY hr))
  have hineq : (ℓ + 1) * dedekindPsi M < 2 * dedekindPsi N := by
    have h1 := mul_dedekindPsi_le hℓ.ne_zero hM0
    have h2 := dedekindPsi_pos hM0
    have h3 := hℓ.two_le
    rw [← hN] at h1
    nlinarith

  have htR : ∀ r ∈ R, 1 ≤ t r := by
    intro r hr
    by_contra h0
    have h0' : t r = 0 := by omega
    have hall : ∀ r' ∈ R, t r' = 0 := by
      intro r' hr'
      obtain ⟨τ, rfl⟩ := hτR r hr r' hr'
      rw [hτt, h0']
    have hsumYR : ∑ y ∈ Y, t y = ∑ y ∈ Y \ R, t y := by
      rw [← Finset.sum_sdiff hRY, Finset.sum_eq_zero hall, add_zero]
    have hle1 : ∑ y ∈ Y \ R, t y ≤ ∑ y ∈ Y \ R, sc y := Finset.sum_le_sum fun y _ => ht_le y
    have hsplit : ∑ y ∈ Y, sc y = ∑ y ∈ Y \ R, sc y + ∑ y ∈ R, sc y := (Finset.sum_sdiff hRY).symm
    have hRle : R.card ≤ ∑ y ∈ R, sc y := by
      rw [Finset.card_eq_sum_ones]; exact Finset.sum_le_sum hsR
    rw [hRcard] at hRle
    rw [hsum_t] at hsumYR
    rw [hsum_s] at hsplit
    omega

  have hsumR : ∑ y ∈ R, t y = dedekindPsi N := by
    apply le_antisymm
    · rw [← hsum_t]; exact Finset.sum_le_sum_of_subset hRY
    · rw [← hRcard, Finset.card_eq_sum_ones]; exact Finset.sum_le_sum htR
  have htR1 : ∀ r ∈ R, t r = 1 := by
    have hsub : ∑ y ∈ R, (t y - 1) = 0 := by
      have : ∑ y ∈ R, t y = ∑ y ∈ R, (t y - 1) + ∑ y ∈ R, 1 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun y hy => (Nat.sub_add_cancel (htR y hy)).symm
      rw [hsumR, ← Finset.card_eq_sum_ones, hRcard] at this
      omega
    intro r hr
    have := (Finset.sum_eq_zero_iff.1 hsub) r hr
    have := htR r hr
    omega
  have htoff : ∀ y ∈ Y \ R, t y = 0 := by
    have : ∑ y ∈ Y \ R, t y = 0 := by
      have h := Finset.sum_sdiff hRY (f := t)
      rw [hsum_t, hsumR] at h
      omega
    exact fun y hy => (Finset.sum_eq_zero_iff.1 this) y hy

  have hmaps : ∀ H, H ∈ CycSub E.toAffine.Point N → E.cyclicQuotientJ H N ∈ R := by
    intro H hH
    by_contra hnot
    have h0 := htoff _ (Finset.mem_sdiff.2 ⟨hvalY H hH, hnot⟩)
    have h1 : 1 ≤ t (E.cyclicQuotientJ H N) :=
      Finset.card_pos.2 ⟨H, Finset.mem_filter.2 ⟨(hmemTF H).2 hH, rfl⟩⟩
    omega
  refine ⟨fun H hH => (hmemR _).1 (hmaps H hH), ?_, ?_⟩
  · intro H hH H' hH' hveq
    have h1 := htR1 _ (hmaps H hH)
    have hmem : H ∈ TF.filter fun H₀ => E.cyclicQuotientJ H₀ N = E.cyclicQuotientJ H N :=
      Finset.mem_filter.2 ⟨(hmemTF H).2 hH, rfl⟩
    have hmem' : H' ∈ TF.filter fun H₀ => E.cyclicQuotientJ H₀ N = E.cyclicQuotientJ H N :=
      Finset.mem_filter.2 ⟨(hmemTF H').2 hH', hveq.symm⟩
    exact Finset.card_le_one.1 h1.le H hmem H' hmem'
  · intro y hy
    have h1 := htR y ((hmemR y).2 hy)
    obtain ⟨H, hH⟩ := Finset.card_pos.1 h1
    rw [Finset.mem_filter, hmemTF] at hH
    exact ⟨H, hH.1, hH.2⟩

end Core

section Transport

variable {K : Type u} [Field K]

theorem Phi_eq_of_level_eq {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) (da : ModularPolynomialData a)
    (db : ModularPolynomialData b) : da.Φ = db.Φ := by
  subst h
  rw [ModularCurve.ModularPolynomialData.eq_all a da db]

theorem exists_eq_of_nsmul_eq_zero {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Injective f) (n : ℕ) [NeZero n]
    (hA : Nat.card {P : A // n • P = 0} = n ^ 2) (hB : Nat.card {Q : B // n • Q = 0} = n ^ 2)
    (Q : B) (hQ : n • Q = 0) : ∃ P : A, n • P = 0 ∧ f P = Q := by
  haveI : Finite {Q : B // n • Q = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hB]; exact pow_ne_zero 2 (NeZero.ne n))
  let g : {P : A // n • P = 0} → {Q : B // n • Q = 0} := fun P =>
    ⟨f P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  have hg : Function.Injective g := fun P P' h => Subtype.ext (hf (congrArg Subtype.val h))
  have hbij := hg.bijective_of_nat_card_le (by rw [hA, hB])
  obtain ⟨P, hP⟩ := hbij.2 ⟨Q, hQ⟩
  exact ⟨P.1, P.2, congrArg Subtype.val hP⟩

theorem natCard_torsion_of_isAlgClosed {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosed Ω] [DecidableEq Ω] (E : WeierstrassCurve k) [E.IsElliptic] (n : ℕ) [NeZero n]
    (hn : (n : Ω) ≠ 0) : Nat.card {Q : (E.baseChange Ω).toAffine.Point // n • Q = 0} = n ^ 2 := by
  obtain ⟨e⟩ := E.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := Ω) hn
  have h1 : Nat.card (Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point n) = n ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  rw [← h1]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun Q => ?_)
  rw [Submodule.mem_torsionBy_iff]
  change n • Q = 0 ↔ ((n : ℤ)) • Q = 0
  rw [natCast_zsmul]

theorem nsmul_eq_zero_of_mem_cycSub {A : Type*} [AddCommGroup A] {H : AddSubgroup A} {n : ℕ}
    (hH : H ∈ CycSub A n) {P : A} (hP : P ∈ H) : n • P = 0 := by
  have := card_nsmul_eq_zero' (G := H) (x := ⟨P, hP⟩)
  rw [hH.2] at this
  exact congrArg Subtype.val this

theorem bijOn_of_bijOn_baseChange {k : Type u} [Field k] {Ω L : Type v} [Field Ω] [Field L]
    [DecidableEq Ω] [DecidableEq L] [IsAlgClosed Ω] [IsAlgClosed L] [Algebra k Ω] [Algebra k L]
    (ι : Ω →ₐ[k] L) (E₀ : WeierstrassCurve k) [E₀.IsElliptic] {N : ℕ} [NeZero N] (hN : (N : Ω) ≠ 0)
    (Φ : Polynomial (Polynomial ℤ))
    (halg : ∀ y : L, (fib Φ (algebraMap k L E₀.j)).IsRoot y → y ∈ Set.range ι)
    (h : Set.BijOn (fun H : AddSubgroup (E₀.baseChange Ω).toAffine.Point =>
        (E₀.baseChange Ω).cyclicQuotientJ H N)
      (CycSub (E₀.baseChange Ω).toAffine.Point N) {y | (fib Φ (algebraMap k Ω E₀.j)).IsRoot y}) :
    Set.BijOn (fun H : AddSubgroup (E₀.baseChange L).toAffine.Point => (E₀.baseChange L).cyclicQuotientJ H N)
      (CycSub (E₀.baseChange L).toAffine.Point N) {y | (fib Φ (algebraMap k L E₀.j)).IsRoot y} := by
  set ιp : (E₀.baseChange Ω).toAffine.Point →+ (E₀.baseChange L).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map ι with hιp
  have hιpinj : Function.Injective ιp := WeierstrassCurve.Affine.Point.map_injective ι
  have hNL : (N : L) ≠ 0 := fun h0 => hN (ι.injective (by rw [map_natCast, h0, map_zero]))

  have hval : ∀ H, (E₀.baseChange L).cyclicQuotientJ (H.map ιp) N = ι ((E₀.baseChange Ω).cyclicQuotientJ H N) :=
    fun H => WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed E₀ ι H N

  have hfib : (fib Φ (algebraMap k Ω E₀.j)).map (ι : Ω →+* L) = fib Φ (algebraMap k L E₀.j) := by
    rw [Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_X, RingHom.coe_coe]
    exact ι.commutes _
  have hrootiff : ∀ y : Ω, (fib Φ (algebraMap k L E₀.j)).IsRoot (ι y) ↔
      (fib Φ (algebraMap k Ω E₀.j)).IsRoot y := fun y => by
    rw [← hfib, IsRoot.def, eval_map, ← RingHom.coe_coe, eval₂_hom, RingHom.coe_coe,
      map_eq_zero_iff ι ι.injective, IsRoot.def]

  have htorΩ := natCard_torsion_of_isAlgClosed (Ω := Ω) E₀ N hN
  have htorL := natCard_torsion_of_isAlgClosed (Ω := L) E₀ N hNL
  have hhit := exists_eq_of_nsmul_eq_zero ιp hιpinj N htorΩ htorL
  have hmapS : ∀ H, H ∈ CycSub (E₀.baseChange Ω).toAffine.Point N →
      H.map ιp ∈ CycSub (E₀.baseChange L).toAffine.Point N := by
    intro H ⟨hc, hcard⟩
    haveI := hc
    let e := H.equivMapOfInjective ιp hιpinj
    exact ⟨isAddCyclic_of_surjective e e.surjective, by rw [← hcard]; exact (Nat.card_congr e.toEquiv).symm⟩
  have hcomapS : ∀ H', H' ∈ CycSub (E₀.baseChange L).toAffine.Point N →
      (H'.comap ιp).map ιp = H' ∧ H'.comap ιp ∈ CycSub (E₀.baseChange Ω).toAffine.Point N := by
    intro H' hH'
    haveI := hH'.1
    have hle : H' ≤ ιp.range := fun Q hQ => by
      obtain ⟨P, -, hP⟩ := hhit Q (nsmul_eq_zero_of_mem_cycSub hH' hQ)
      exact ⟨P, hP⟩
    have hmap : (H'.comap ιp).map ιp = H' := by
      rw [AddSubgroup.map_comap_eq, inf_eq_right.2 hle]
    let e := (H'.comap ιp).equivMapOfInjective ιp hιpinj
    have e' : (H'.comap ιp) ≃+ H' := e.trans (AddEquiv.addSubgroupCongr hmap)
    exact ⟨hmap, isAddCyclic_of_surjective e'.symm e'.symm.surjective,
      by rw [← hH'.2]; exact Nat.card_congr e'.toEquiv⟩
  refine ⟨?_, ?_, ?_⟩
  · intro H' hH'
    obtain ⟨hmap, hH⟩ := hcomapS H' hH'
    change (fib Φ _).IsRoot ((E₀.baseChange L).cyclicQuotientJ H' N)
    rw [← hmap, hval, hrootiff]
    exact h.mapsTo hH
  · intro H₁ hH₁ H₂ hH₂ heq
    obtain ⟨hmap₁, hH₁'⟩ := hcomapS H₁ hH₁
    obtain ⟨hmap₂, hH₂'⟩ := hcomapS H₂ hH₂
    change (E₀.baseChange L).cyclicQuotientJ H₁ N = (E₀.baseChange L).cyclicQuotientJ H₂ N at heq
    rw [← hmap₁, ← hmap₂, hval, hval] at heq
    have := h.injOn hH₁' hH₂' (ι.injective heq)
    rw [← hmap₁, ← hmap₂, this]
  · intro y hy
    obtain ⟨y₀, rfl⟩ := halg y hy
    obtain ⟨H, hH, hHy⟩ := h.surjOn ((hrootiff y₀).1 hy)
    exact ⟨H.map ιp, hmapS H hH, by change (E₀.baseChange L).cyclicQuotientJ _ N = _; rw [hval]; exact congrArg ι hHy⟩

def vcInvHom {L : Type v} [Field L] [DecidableEq L] (C : VariableChange L) (W : WeierstrassCurve L) :
    W.toAffine.Point →+ (C • W).toAffine.Point where
  toFun := Affine.Point.vcInvFun C W
  map_zero' := rfl
  map_add' := Affine.Point.vcInvFun_add C W

theorem bijOn_of_variableChange {L : Type v} [Field L] [DecidableEq L] (C : VariableChange L)
    (E E' : WeierstrassCurve L) (hCE : C • E = E') {N : ℕ} (hN : (N : L) ≠ 0) (T : Set L)
    (h : Set.BijOn (fun H : AddSubgroup E'.toAffine.Point => E'.cyclicQuotientJ H N)
      (CycSub E'.toAffine.Point N) T) :
    Set.BijOn (fun H : AddSubgroup E.toAffine.Point => E.cyclicQuotientJ H N) (CycSub E.toAffine.Point N) T := by
  subst hCE
  set e : E.toAffine.Point →+ (C • E).toAffine.Point := vcInvHom C E with he
  have hesurj : Function.Surjective e := fun P => ⟨Affine.Point.vcFun C E P, Affine.Point.vcFun_leftInverse P⟩
  have heinj : Function.Injective e :=
    Function.LeftInverse.injective (g := Affine.Point.vcFun C E) Affine.Point.vcFun_rightInverse
  have hval : ∀ H, (C • E).cyclicQuotientJ (H.map e) N = E.cyclicQuotientJ H N := by
    intro H
    refine WeierstrassCurve.cyclicQuotientJ_variableChange_eq C E H (H.map e) (fun P => ?_) N hN
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      change Affine.Point.vcFun C E (Affine.Point.vcInvFun C E Q) ∈ H
      rwa [Affine.Point.vcFun_rightInverse]
    · intro hP
      exact ⟨_, hP, Affine.Point.vcFun_leftInverse P⟩
  have hmapS : ∀ H, H ∈ CycSub E.toAffine.Point N ↔ H.map e ∈ CycSub (C • E).toAffine.Point N := by
    intro H
    let f := H.equivMapOfInjective e heinj
    constructor
    · rintro ⟨hc, hcard⟩
      haveI := hc
      exact ⟨isAddCyclic_of_surjective f f.surjective, by rw [← hcard]; exact (Nat.card_congr f.toEquiv).symm⟩
    · rintro ⟨hc, hcard⟩
      haveI := hc
      exact ⟨isAddCyclic_of_surjective f.symm f.symm.surjective,
        by rw [← hcard]; exact Nat.card_congr f.toEquiv⟩
  have hcomap : ∀ H' : AddSubgroup (C • E).toAffine.Point, (H'.comap e).map e = H' := fun H' => by
    rw [AddSubgroup.map_comap_eq, AddMonoidHom.range_eq_top.2 hesurj, top_inf_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro H hH
    change E.cyclicQuotientJ H N ∈ T
    rw [← hval]
    exact h.mapsTo ((hmapS H).1 hH)
  · intro H₁ hH₁ H₂ hH₂ heq
    change E.cyclicQuotientJ H₁ N = E.cyclicQuotientJ H₂ N at heq
    rw [← hval, ← hval] at heq
    exact AddSubgroup.map_injective heinj (h.injOn ((hmapS H₁).1 hH₁) ((hmapS H₂).1 hH₂) heq)
  · intro y hy
    obtain ⟨H', hH', hy'⟩ := h.surjOn hy
    refine ⟨H'.comap e, (hmapS _).2 (by rw [hcomap]; exact hH'), ?_⟩
    change E.cyclicQuotientJ _ N = y
    rw [← hval, hcomap]
    exact hy'

end Transport

theorem bijOn_one (K : Type u) [Field K] (data : ModularPolynomialData 1)
    (L : Type v) [Field L] [DecidableEq L] (E : WeierstrassCurve L) [E.IsElliptic] :
    Set.BijOn (fun H : AddSubgroup E.toAffine.Point => E.cyclicQuotientJ H 1)
      (CycSub E.toAffine.Point 1) {y | (fib data.Φ E.j).IsRoot y} := by
  have hΦ : data.Φ = X - C X := by
    rw [ModularCurve.ModularPolynomialData.eq_all 1 data modularPolynomialDataOne]; rfl
  have hroot : ∀ y, (fib data.Φ E.j).IsRoot y ↔ y = E.j := fun y => by
    rw [hΦ, IsRoot.def]
    simp only [Polynomial.map_sub, map_X, map_C, coe_eval₂RingHom, eval₂_X, eval_sub, eval_X, eval_C]
    exact sub_eq_zero
  have hval : ∀ H : AddSubgroup E.toAffine.Point, E.cyclicQuotientJ H 1 = E.j := fun H => by
    rw [cyclicQuotientJ_one, WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
      inv_mul_eq_div]
  have hcyc : ∀ H : AddSubgroup E.toAffine.Point, H ∈ CycSub E.toAffine.Point 1 ↔ H = ⊥ := fun H => by
    constructor
    · exact fun h => AddSubgroup.card_eq_one.1 h.2
    · rintro rfl
      exact ⟨inferInstance, AddSubgroup.card_eq_one.2 rfl⟩
  refine ⟨fun H _ => (hroot _).2 (hval H), ?_, ?_⟩
  · intro H₁ hH₁ H₂ hH₂ _
    rw [(hcyc H₁).1 hH₁, (hcyc H₂).1 hH₂]
  · intro y hy
    exact ⟨⊥, (hcyc ⊥).2 rfl, (hval ⊥).trans ((hroot y).1 hy).symm⟩

theorem bijOn_step (K : Type u) [Field K] {ℓ M : ℕ} [Fact ℓ.Prime] [NeZero M]
    (dℓ : ModularPolynomialData ℓ) (dM : ModularPolynomialData M) (dN : ModularPolynomialData (ℓ * M))
    (hmin : (ℓ * M).minFac = ℓ)
    (L : Type v) [Field L] [DecidableEq L] [IsAlgClosed L] [Algebra K L] (hNL : ((ℓ * M : ℕ) : L) ≠ 0)
    (IH : ∀ (Ω : Type v) [Field Ω] [DecidableEq Ω] [IsAlgClosed Ω] [Algebra K Ω], (M : Ω) ≠ 0 →
      ∀ (W : WeierstrassCurve Ω) [W.IsElliptic], Transcendental K W.j →
        Set.BijOn (fun C : AddSubgroup W.toAffine.Point => W.cyclicQuotientJ C M)
          (CycSub W.toAffine.Point M) {y | (fib dM.Φ W.j).IsRoot y})
    (E : WeierstrassCurve L) [E.IsElliptic] (hE : Transcendental K E.j) :
    Set.BijOn (fun H : AddSubgroup E.toAffine.Point => E.cyclicQuotientJ H (ℓ * M))
      (CycSub E.toAffine.Point (ℓ * M)) {y | (fib dN.Φ E.j).IsRoot y} := by
  classical
  set N := ℓ * M with hN
  set x := E.j with hx
  have hNK : (N : K) ≠ 0 := fun h => hNL (by
    have := congrArg (algebraMap K L) h; rwa [map_natCast, map_zero] at this)

  set F := RatFunc K with hF
  letI : DecidableEq F := Classical.decEq F
  set φK : Polynomial K →+* L := (Polynomial.aeval (R := K) x).toRingHom with hφK
  have hφKinj : Function.Injective φK := transcendental_iff_injective.1 hE
  have hφK0 : nonZeroDivisors (Polynomial K) ≤ (nonZeroDivisors L).comap φK := fun p hp =>
    mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero hp (hφKinj (h.trans (map_zero φK).symm)))
  set φF : F →+* L := RatFunc.liftRingHom φK hφK0 with hφF
  letI : Algebra F L := φF.toAlgebra
  set XF : F := algebraMap (Polynomial K) F X with hXF
  have hφFX : algebraMap F L XF = x := by
    change φF XF = x
    rw [hφF, hXF, RatFunc.liftRingHom_algebraMap]
    simp [hφK]
  haveI : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap K L c = φF (algebraMap K F c)
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) F c, hφF, RatFunc.liftRingHom_algebraMap, hφK,
      Polynomial.algebraMap_apply]
    change _ = Polynomial.aeval x (C c)
    rw [aeval_C]

  set Ω := algebraicClosure F L with hΩ
  letI : DecidableEq Ω := Classical.decEq _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : IsScalarTower K Ω L := IsScalarTower.of_algebraMap_eq fun c => rfl
  have hMK : (M : K) ≠ 0 := fun h => hNK (by rw [hN, Nat.cast_mul, h, mul_zero])
  have hMΩ : (M : Ω) ≠ 0 := fun h => hMK ((algebraMap K Ω).injective (by rw [map_natCast, h, map_zero]))
  have hNΩ : (N : Ω) ≠ 0 := fun h => hNK ((algebraMap K Ω).injective (by rw [map_natCast, h, map_zero]))

  set E_F : WeierstrassCurve F := WeierstrassCurve.ofJ XF with hE_F
  have hEFj : E_F.j = XF := WeierstrassCurve.ofJ_j XF
  have hxL : algebraMap F L E_F.j = x := by rw [hEFj, hφFX]
  have hxΩ : Transcendental K (algebraMap F Ω E_F.j) := by
    rw [← transcendental_algebraMap_iff (algebraMap Ω L).injective, ← IsScalarTower.algebraMap_apply,
      hxL]
    exact hE

  set pF : Polynomial F := (dN.Φ.map (Polynomial.mapRingHom (Int.castRingHom K))).map
    (algebraMap (Polynomial K) F) with hpFdef
  have hirr : Irreducible pF :=
    ModularCurve.ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero K (ℓ * M) dN hNK
  have hpFmap : ∀ (T : Type v) [Field T] [Algebra F T],
      pF.map (algebraMap F T) = fib dN.Φ (algebraMap F T E_F.j) := by
    intro T _ _
    rw [hpFdef, Polynomial.map_map, Polynomial.map_map, hEFj]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_X, coe_eval₂RingHom, eval₂_X]
    rfl

  have hcore := bijOn_core K hNK dℓ dM dN hmin E_F hxΩ pF (hpFmap Ω) hirr
    (fun W _ hW => IH Ω hMΩ W hW)

  have halg : ∀ y : L, (fib dN.Φ (algebraMap F L E_F.j)).IsRoot y → y ∈ Set.range (algebraicClosure F L).val := by
    intro y hy
    rw [← hpFmap L, IsRoot.def, eval_map, ← aeval_def] at hy
    have halg : IsAlgebraic F y := ⟨pF, hirr.ne_zero, hy⟩
    exact ⟨⟨y, mem_algebraicClosure_iff.2 halg⟩, rfl⟩
  have hL := bijOn_of_bijOn_baseChange (algebraicClosure F L).val E_F hNΩ dN.Φ halg hcore
  rw [hxL] at hL

  haveI : (E_F.baseChange L).IsElliptic := show (E_F.map _).IsElliptic from inferInstance
  have hj : E.j = (E_F.baseChange L).j := by
    rw [← hx, ← hxL]; change _ = (E_F.map (algebraMap F L)).j; exact (E_F.map_j _).symm
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq E _ hj
  exact bijOn_of_variableChange C E _ hC hNL _ hL

end P2MKcKI
p2m_reactivate "P2MW.S_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j.P2MKcKI"

open P2MKcKI in
theorem P2MKcKI.main (K : Type u) [Field K] : ∀ (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (L : Type v) [Field L] [DecidableEq L] [IsAlgClosed L] [Algebra K L], (N : L) ≠ 0 →
    ∀ (E : WeierstrassCurve L) [E.IsElliptic], Transcendental K E.j →
    Set.BijOn (fun H : AddSubgroup E.toAffine.Point => E.cyclicQuotientJ H N)
      (CycSub E.toAffine.Point N) {y | (fib data.Φ E.j).IsRoot y} := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro _ data L _ _ _ _ hNL E _ hE
  by_cases h1 : N = 1
  · subst h1; exact bijOn_one K data L E
  · have hN0 : N ≠ 0 := NeZero.ne N
    have hℓ : N.minFac.Prime := Nat.minFac_prime h1
    haveI : Fact N.minFac.Prime := ⟨hℓ⟩
    obtain ⟨M, hM⟩ : N.minFac ∣ N := Nat.minFac_dvd N
    have hM0 : M ≠ 0 := by rintro rfl; exact hN0 (by rw [hM, mul_zero])
    haveI : NeZero M := ⟨hM0⟩
    have hMlt : M < N := by
      have := hℓ.two_le
      have : 0 < M := Nat.pos_of_ne_zero hM0
      rw [hM]; nlinarith
    obtain ⟨dℓ⟩ := ModularCurve.nonempty_modularPolynomialData N.minFac
    obtain ⟨dM⟩ := ModularCurve.nonempty_modularPolynomialData M
    obtain ⟨dN⟩ := ModularCurve.nonempty_modularPolynomialData (N.minFac * M)
    have hΦ : data.Φ = dN.Φ := Phi_eq_of_level_eq hM data dN
    have hmin : (N.minFac * M).minFac = N.minFac := by rw [← hM]
    have hNL' : ((N.minFac * M : ℕ) : L) ≠ 0 := by rw [← hM]; exact hNL
    have step := bijOn_step K dℓ dM dN hmin L hNL'
      (fun Ω _ _ _ _ hMΩ W _ hW => ih M hMlt dM Ω hMΩ W hW) E hE
    rw [hΦ]
    have key : ∀ n : ℕ, n = N →
        Set.BijOn (fun H : AddSubgroup E.toAffine.Point => E.cyclicQuotientJ H n)
          (CycSub E.toAffine.Point n) {y | (fib dN.Φ E.j).IsRoot y} →
        Set.BijOn (fun H : AddSubgroup E.toAffine.Point => E.cyclicQuotientJ H N)
          (CycSub E.toAffine.Point N) {y | (fib dN.Φ E.j).IsRoot y} := by
      rintro n rfl h; exact h
    exact key _ hM.symm step

open P2MKcKI in
theorem solution
    (K : Type u) [Field K] (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (L : Type v) [Field L] [DecidableEq L] [IsAlgClosed L] [Algebra K L]
    (hN : (N : L) ≠ 0) (E : WeierstrassCurve L) [E.IsElliptic] (hE : Transcendental K E.j) :
    Set.BijOn (fun H : AddSubgroup E.toAffine.Point => E.cyclicQuotientJ H N)
      {H | IsAddCyclic H ∧ Nat.card H = N}
      {y | (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom L) E.j)).IsRoot y} :=
  P2MKcKI.main K N data L hN E hE

end
p2m_reactivate "P2MW.S_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j.P2MKcKI"

end S_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
end P2MW
export P2MW.S_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j (solution)
