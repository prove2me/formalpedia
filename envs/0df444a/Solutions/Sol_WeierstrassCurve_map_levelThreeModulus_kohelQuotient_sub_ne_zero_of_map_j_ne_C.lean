-- Prove2me | solution 1 for WeierstrassCurve.map_levelThreeModulus_kohelQuotient_sub_ne_zero_of_map_j_ne_C
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/d64c389d-a8ff-5827-82fc-65d427f2caeb

import Mathlib
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_KernelPolynomial
import Definitions.Def_WeierstrassCurve_KohelQuotient
import Definitions.Def_WeierstrassCurve_LevelThreeModulus
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_apply_j_ne_apply_j_of_j_map_eq_veluQuotient_j_of_ne_C
import Theorems.Thm_WeierstrassCurve_exists_reduceHom_eq_and_map_eq_kernelPolynomial_oddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_kohelQuotient_kernelPolynomial_eq_veluQuotient
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_WeierstrassCurve_exists_variableChange_of_levelThreeModulus_eq
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_map_levelThreeModulus_kohelQuotient_sub_ne_zero_of_map_j_ne_C
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open Polynomial IsLocalRing

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.Equation variableChange_j a₃ map_map a₁ map Ψ₃ map_j a₄ a₂ a₆ Affine.Point.some map_preΨ' reduction preΨ' toAffine Affine.Point Affine.Equation.map map_Δ Affine.equation_iff_nonsingular map_Ψ₃ Δ Affine.equation_iff preΨ'_three j Affine.Point.coordsOrZero oddOrderSummingSet mem_oddOrderSummingSet kernelPolynomial map_kernelPolynomial_of_injOn kohelQuotient map_kohelQuotient veluQuotient deuringA₃ levelThreeModulus levelThreeModulus_map_of_isUnit ratPointMap_zero ratPointMap_some ratPointMap_injective ratPointHom ratPointMap apply_j_ne_apply_j_of_j_map_eq_veluQuotient_j_of_ne_C exists_reduceHom_eq_and_map_eq_kernelPolynomial_oddOrderSummingSet kohelQuotient_kernelPolynomial_eq_veluQuotient exists_variableChange_of_levelThreeModulus_eq Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi"
p2m_open "WeierstrassCurve"

namespace LevelThreeDisc

section Cast

variable {F : Type*} [Field F] [DecidableEq F]

def castPoint {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    W₂.toAffine.Point := e ▸ P

theorem addOrderOf_castPoint {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    addOrderOf (castPoint e P) = addOrderOf P := by
  subst e; rfl

theorem oddOrderSummingSet_castPoint {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂)
    (P : W₁.toAffine.Point) (n : ℕ) :
    W₂.oddOrderSummingSet (castPoint e P) n = W₁.oddOrderSummingSet P n := by
  subst e; rfl

end Cast

section RatPoint

variable {F K : Type} [Field F] [Field K] [DecidableEq F] [DecidableEq K] (f : F →+* K)
  {W : WeierstrassCurve F}

theorem coordsOrZero_ratPointHom (P : W.toAffine.Point) :
    (ratPointHom f P).coordsOrZero = Prod.map f f P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · show (ratPointMap f (0 : W.toAffine.Point)).coordsOrZero = _
    rw [ratPointMap_zero]
    simp [Affine.Point.coordsOrZero]
  · show (ratPointMap f (.some x y h)).coordsOrZero = _
    rw [ratPointMap_some]
    rfl

theorem oddOrderSummingSet_ratPointHom (Q : W.toAffine.Point) (n : ℕ) :
    (W.map f).oddOrderSummingSet (ratPointHom f Q) n =
      (W.oddOrderSummingSet Q n).image (Prod.map f f) := by
  simp only [oddOrderSummingSet, Finset.image_image]
  congr 1
  funext k
  simp only [Function.comp_apply, ← map_nsmul, coordsOrZero_ratPointHom]

end RatPoint

section ThreeTorsion

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in

theorem exists_equation_of_isAlgClosed [IsAlgClosed F] (x : F) :
    ∃ y : F, W.toAffine.Equation x y := by

  let b : F := W.a₁ * x + W.a₃
  let c : F := -(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
  let p : F[X] := X ^ 2 + (C b * X + C c)
  have hlt : (C b * X + C c).degree < (X ^ 2 : F[X]).degree := by
    rw [degree_X_pow]
    refine lt_of_le_of_lt (degree_add_le _ _) ?_
    refine max_lt ?_ ?_
    · exact lt_of_le_of_lt (degree_C_mul_X_le b) (by norm_num)
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
  have hdeg : p.degree = 2 := by
    show (X ^ 2 + (C b * X + C c)).degree = 2
    rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]
    rfl
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root p (by rw [hdeg]; exact two_ne_zero)
  refine ⟨y, ?_⟩
  rw [Affine.equation_iff]
  have : y ^ 2 + (b * y + c) = 0 := by
    have := hy
    simp only [p, IsRoot.def, eval_add, eval_pow, eval_X, eval_mul, eval_C] at this
    exact this
  simp only [b, c] at this
  linear_combination this

theorem three_smul_eq_zero_of_eval_Ψ₃ [W.IsElliptic] {x y : F} (h : W.toAffine.Nonsingular x y)
    (hx : W.Ψ₃.eval x = 0) : (3 : ℤ) • (Affine.Point.some x y h) = 0 := by
  have h3 : (3 : ℕ) • Affine.Point.some x y h = 0 := by
    rw [Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W (by decide) h, preΨ'_three]
    exact hx
  exact_mod_cast h3

end ThreeTorsion

theorem j_congr {R : Type*} [CommRing R] {X Y : WeierstrassCurve R} [X.IsElliptic] [Y.IsElliptic]
    (e : X = Y) : X.j = Y.j := by
  subst e; rfl

theorem equation_of_mem_oddOrderSummingSet {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1)
    {P : F × F} (hP : P ∈ W.oddOrderSummingSet Q n) : W.toAffine.Equation P.1 P.2 := by
  rw [mem_oddOrderSummingSet] at hP
  obtain ⟨k, hk1, hkn, rfl⟩ := hP
  have hk0 : k • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  rcases hkQ : k • Q with _ | ⟨x, y, h⟩
  · exact absurd hkQ hk0
  · exact h.1

theorem map_kohelQuotient_j_ne {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [DecidableEq k] (π : 𝒪 →+* k) (hπ : Function.Surjective π)
    (E : WeierstrassCurve (PowerSeries 𝒪)) [E.IsElliptic]
    (hj : PowerSeries.map π E.j ≠
      PowerSeries.C (PowerSeries.constantCoeff (PowerSeries.map π E.j)))
    {n : ℕ} (hm : ((2 * n + 1 : ℕ) : k) ≠ 0) (hsq : ¬ IsSquare (2 * n + 1))
    (Q₀ : (E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).toAffine.Point)
    (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    {h : Polynomial (PowerSeries 𝒪)} (hh : h.Monic) (hdvd : h ∣ E.preΨ' (2 * n + 1))
    (hmap : h.map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) =
      WeierstrassCurve.kernelPolynomial
        ((E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).oddOrderSummingSet Q₀ n))
    [(E.kohelQuotient h).IsElliptic] :
    PowerSeries.map π (E.kohelQuotient h).j ≠ PowerSeries.map π E.j := by
  classical
  let cc : PowerSeries 𝒪 →+* 𝒪 := PowerSeries.constantCoeff (R := 𝒪)
  let ρ : PowerSeries 𝒪 →+* PowerSeries k := PowerSeries.map π
  set E' : WeierstrassCurve (PowerSeries 𝒪) := E.kohelQuotient h with hE'
  set m : ℕ := 2 * n + 1 with hm_def
  show ρ E'.j ≠ ρ E.j
  have hπcc : Function.Surjective (π.comp cc) := fun a => by
    obtain ⟨b, rfl⟩ := hπ a
    exact ⟨PowerSeries.C b, by simp [cc]⟩

  let L : Type := AlgebraicClosure (FractionRing (PowerSeries 𝒪))
  let f : PowerSeries 𝒪 →+* L := algebraMap (PowerSeries 𝒪) L
  have hf : Function.Injective f := by
    change Function.Injective (algebraMap (PowerSeries 𝒪) L)
    rw [IsScalarTower.algebraMap_eq (PowerSeries 𝒪) (FractionRing (PowerSeries 𝒪)) L]
    exact (algebraMap (FractionRing (PowerSeries 𝒪)) L).injective.comp
      (IsFractionRing.injective (PowerSeries 𝒪) (FractionRing (PowerSeries 𝒪)))
  haveI : CharZero L := by
    have hC : Function.Injective (PowerSeries.C (R := 𝒪)) := PowerSeries.C_injective
    haveI : CharZero (PowerSeries 𝒪) := charZero_of_injective_ringHom hC
    exact charZero_of_injective_ringHom hf

  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  let toA : PowerSeries 𝒪 →+* A := f.codRestrict A hA
  have hunit : ∀ x, IsUnit (toA x) → IsUnit x := fun x hx =>
    (hloc.map_nonunit x hx)
  haveI : HenselianLocalRing A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A

  let EA : WeierstrassCurve A := E.map toA
  have hΔA : (EA.map (residue A)).Δ ≠ 0 := by
    rw [map_Δ, map_Δ, residue_ne_zero_iff_isUnit]
    exact (E.isUnit_Δ).map toA

  have hker : RingHom.ker (π.comp cc) ≤ RingHom.ker ((residue A).comp toA) := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    rw [RingHom.comp_apply, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : IsUnit ((π.comp cc) x) := (hunit x hu).map (π.comp cc)
    rw [hx] at h1
    exact not_isUnit_zero h1
  let ψ : k →+* ResidueField A :=
    (π.comp cc).liftOfRightInverse (Function.surjInv hπcc) (Function.rightInverse_surjInv hπcc)
      ⟨(residue A).comp toA, hker⟩
  have hψ : ∀ x, ψ ((π.comp cc) x) = residue A (toA x) := fun x =>
    (π.comp cc).liftOfRightInverse_comp_apply _ _ ⟨(residue A).comp toA, hker⟩ x
  have hψcomp : ψ.comp (π.comp cc) = (residue A).comp toA := RingHom.ext hψ
  have hcurve : (E.map (π.comp cc)).map ψ = EA.map (residue A) := by
    rw [map_map, hψcomp, ← map_map]

  let Q₀A : (EA.map (residue A)).toAffine.Point := castPoint hcurve (ratPointHom ψ Q₀)
  have hQ₀A : addOrderOf Q₀A = m := by
    show addOrderOf (castPoint hcurve (ratPointHom ψ Q₀)) = m
    rw [addOrderOf_castPoint]
    exact (addOrderOf_injective (ratPointHom ψ)
      (fun a b hab => ratPointMap_injective ψ hab) Q₀).trans hQ₀
  have hmA : ((2 * n + 1 : ℕ) : ResidueField A) ≠ 0 := by
    rw [← map_natCast ψ]
    exact (map_ne_zero ψ).mpr hm
  have hdvdA : h.map toA ∣ EA.preΨ' (2 * n + 1) := by
    rw [map_preΨ']; exact Polynomial.map_dvd toA hdvd
  have hmapA : (h.map toA).map (residue A) =
      kernelPolynomial ((EA.map (residue A)).oddOrderSummingSet Q₀A n) := by
    show _ = kernelPolynomial ((EA.map (residue A)).oddOrderSummingSet
      (castPoint hcurve (ratPointHom ψ Q₀)) n)
    rw [oddOrderSummingSet_castPoint hcurve, oddOrderSummingSet_ratPointHom,
      ← map_kernelPolynomial_of_injOn ψ _ ((ψ.injective.prodMap ψ.injective).injOn),
      ← hmap, Polynomial.map_map, Polynomial.map_map, hψcomp]
  obtain ⟨Q, hQord, -, hQker⟩ :=
    exists_reduceHom_eq_and_map_eq_kernelPolynomial_oddOrderSummingSet hΔA hmA Q₀A hQ₀A
      (hh.map toA) hdvdA hmapA

  let φ : PowerSeries 𝒪 →+* L := A.subtype.comp toA
  have hφf : φ = f := RingHom.ext fun x => rfl
  have hφ : Function.Injective φ := hφf ▸ hf
  have hEφ : (EA.map A.subtype) = E.map φ := map_map E toA A.subtype
  let QL : (E.map φ).toAffine.Point := castPoint hEφ Q
  have hQL : addOrderOf QL = m := by
    show addOrderOf (castPoint hEφ Q) = m
    rw [addOrderOf_castPoint, hQord]
  set SQ := (E.map φ).oddOrderSummingSet QL n with hSQ
  have hSQ' : (EA.map A.subtype).oddOrderSummingSet Q n = SQ := by
    rw [hSQ]
    show _ = (E.map φ).oddOrderSummingSet (castPoint hEφ Q) n
    rw [oddOrderSummingSet_castPoint hEφ]
  have hhφ : h.map φ = kernelPolynomial SQ := by
    rw [← hSQ', ← hQker, Polynomial.map_map]
  have hKQ : (E.map φ).kohelQuotient (kernelPolynomial SQ) = (E.map φ).veluQuotient SQ :=
    kohelQuotient_kernelPolynomial_eq_veluQuotient _ _
      (fun P hP => equation_of_mem_oddOrderSummingSet _ QL n hQL hP)
  have hE'φ : E'.map φ = (E.map φ).veluQuotient SQ := by
    rw [hE', map_kohelQuotient E φ hh, hhφ, hKQ]
  have hΔv : ((E.map φ).veluQuotient SQ).Δ ≠ 0 := by
    rw [← hE'φ]; exact (E'.map φ).isUnit_Δ.ne_zero
  have hE'v : haveI : ((E.map φ).veluQuotient SQ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔv⟩
      (E'.map φ).j = ((E.map φ).veluQuotient SQ).j := by
    haveI : ((E.map φ).veluQuotient SQ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔv⟩
    exact j_congr hE'φ
  exact apply_j_ne_apply_j_of_j_map_eq_veluQuotient_j_of_ne_C E E' φ hφ hsq QL hQL hΔv hE'v ρ hj

theorem main {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [DecidableEq k] (π : 𝒪 →+* k) (hπ : Function.Surjective π)
    (h3 : (3 : k) ≠ 0)
    (E : WeierstrassCurve (PowerSeries 𝒪)) [E.IsElliptic]
    (hj : PowerSeries.map π E.j ≠
      PowerSeries.C (PowerSeries.constantCoeff (PowerSeries.map π E.j)))
    {n : ℕ} (hm : ((2 * n + 1 : ℕ) : k) ≠ 0) (hsq : ¬ IsSquare (2 * n + 1))
    (Q₀ : (E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).toAffine.Point)
    (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    {h : Polynomial (PowerSeries 𝒪)} (hh : h.Monic) (hdvd : h ∣ E.preΨ' (2 * n + 1))
    (hmap : h.map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) =
      WeierstrassCurve.kernelPolynomial
        ((E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).oddOrderSummingSet Q₀ n))
    [(E.kohelQuotient h).IsElliptic]
    {x₁ y₁ x₂ : PowerSeries 𝒪} (hP₁ : E.toAffine.Equation x₁ y₁)
    (hx₁ : E.Ψ₃.eval x₁ = 0) (hx₂ : E.Ψ₃.eval x₂ = 0)
    (hA₃ : IsUnit (E.deuringA₃ x₁ y₁)) (hx : PowerSeries.map π (x₂ - x₁) ≠ 0)
    {x₁' y₁' x₂' : PowerSeries 𝒪} (hP₁' : (E.kohelQuotient h).toAffine.Equation x₁' y₁')
    (hx₁' : (E.kohelQuotient h).Ψ₃.eval x₁' = 0) (hx₂' : (E.kohelQuotient h).Ψ₃.eval x₂' = 0)
    (hA₃' : IsUnit ((E.kohelQuotient h).deuringA₃ x₁' y₁'))
    (hx' : PowerSeries.map π (x₂' - x₁') ≠ 0) :
    PowerSeries.map π ((E.kohelQuotient h).levelThreeModulus x₁' y₁' x₂'
      - E.levelThreeModulus x₁ y₁ x₂) ≠ 0 := by
  classical
  intro hF
  let ρ : PowerSeries 𝒪 →+* PowerSeries k := PowerSeries.map π
  set E' : WeierstrassCurve (PowerSeries 𝒪) := E.kohelQuotient h with hE'

  have hGD : ρ E'.j ≠ ρ E.j := map_kohelQuotient_j_ne π hπ E hj hm hsq Q₀ hQ₀ hh hdvd hmap

  apply hGD

  let L₂ : Type := AlgebraicClosure (FractionRing (PowerSeries k))
  let ι : PowerSeries k →+* L₂ := algebraMap (PowerSeries k) L₂
  have hι : Function.Injective ι := by
    change Function.Injective (algebraMap (PowerSeries k) L₂)
    rw [IsScalarTower.algebraMap_eq (PowerSeries k) (FractionRing (PowerSeries k)) L₂]
    exact (algebraMap (FractionRing (PowerSeries k)) L₂).injective.comp
      (IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k)))
  let σ : PowerSeries 𝒪 →+* L₂ := ι.comp ρ
  have hσ : ∀ x, σ x = ι (ρ x) := fun x => rfl
  have h3L : (3 : L₂) ≠ 0 := by
    have h3k : (3 : PowerSeries k) ≠ 0 := fun h0 => h3 (by
      have := congrArg (PowerSeries.constantCoeff (R := k)) h0
      simpa [map_ofNat] using this)
    have : ι 3 ≠ 0 := (map_ne_zero_iff ι hι).mpr h3k
    rwa [map_ofNat] at this

  have hns : ∀ (V : WeierstrassCurve (PowerSeries 𝒪)) [V.IsElliptic] {x y : L₂},
      (V.map σ).toAffine.Equation x y → (V.map σ).toAffine.Nonsingular x y := by
    intro V _ x y hxy
    exact (Affine.equation_iff_nonsingular (W := (V.map σ).toAffine)).mp hxy

  have hev : ∀ (V : WeierstrassCurve (PowerSeries 𝒪)) {e : PowerSeries 𝒪},
      V.Ψ₃.eval e = 0 → (V.map σ).Ψ₃.eval (σ e) = 0 := by
    intro V e hVe
    rw [map_Ψ₃, eval_map, eval₂_hom, hVe, map_zero]

  have hne : σ x₁ ≠ σ x₂ := by
    intro h12
    apply hx
    apply hι
    rw [map_zero, ← hσ, map_sub, h12, sub_self]
  have hne' : σ x₁' ≠ σ x₂' := by
    intro h12
    apply hx'
    apply hι
    rw [map_zero, ← hσ, map_sub, h12, sub_self]

  have heq₁ : (E.map σ).toAffine.Equation (σ x₁) (σ y₁) := Affine.Equation.map σ hP₁
  have h₁ : (E.map σ).toAffine.Nonsingular (σ x₁) (σ y₁) := hns E heq₁
  obtain ⟨y₂, heq₂⟩ := exists_equation_of_isAlgClosed (E.map σ) (σ x₂)
  have h₂ : (E.map σ).toAffine.Nonsingular (σ x₂) y₂ := hns E heq₂
  have hP₁3 : (3 : ℤ) • (Affine.Point.some _ _ h₁) = 0 :=
    three_smul_eq_zero_of_eval_Ψ₃ _ h₁ (hev E hx₁)
  have hP₂3 : (3 : ℤ) • (Affine.Point.some _ _ h₂) = 0 :=
    three_smul_eq_zero_of_eval_Ψ₃ _ h₂ (hev E hx₂)

  have heq₁' : (E'.map σ).toAffine.Equation (σ x₁') (σ y₁') := Affine.Equation.map σ hP₁'
  have h₁' : (E'.map σ).toAffine.Nonsingular (σ x₁') (σ y₁') := hns E' heq₁'
  obtain ⟨y₂', heq₂'⟩ := exists_equation_of_isAlgClosed (E'.map σ) (σ x₂')
  have h₂' : (E'.map σ).toAffine.Nonsingular (σ x₂') y₂' := hns E' heq₂'
  have hP₁3' : (3 : ℤ) • (Affine.Point.some _ _ h₁') = 0 :=
    three_smul_eq_zero_of_eval_Ψ₃ _ h₁' (hev E' hx₁')
  have hP₂3' : (3 : ℤ) • (Affine.Point.some _ _ h₂') = 0 :=
    three_smul_eq_zero_of_eval_Ψ₃ _ h₂' (hev E' hx₂')

  have hτ : (E.map σ).levelThreeModulus (σ x₁) (σ y₁) (σ x₂) =
      (E'.map σ).levelThreeModulus (σ x₁') (σ y₁') (σ x₂') := by
    rw [levelThreeModulus_map_of_isUnit σ hA₃, levelThreeModulus_map_of_isUnit σ hA₃']
    have key := congrArg ι hF
    rw [map_zero, ← hσ, map_sub] at key
    exact (sub_eq_zero.mp key).symm

  obtain ⟨-, -, γ, hγ, -, -, -⟩ :=
    exists_variableChange_of_levelThreeModulus_eq h3L (E.map σ) (E'.map σ)
      h₁ h₂ hP₁3 hP₂3 hne h₁' h₂' hP₁3' hP₂3' hne' hτ

  have hjj : (E'.map σ).j = (E.map σ).j := by
    rw [← j_congr hγ]; exact variableChange_j _ γ
  apply hι
  rw [← hσ, ← hσ, ← map_j, ← map_j]
  exact hjj

end LevelThreeDisc

end WeierstrassCurve

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_map_levelThreeModulus_kohelQuotient_sub_ne_zero_of_map_j_ne_C.WeierstrassCurve in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [DecidableEq k] (π : 𝒪 →+* k) (hπ : Function.Surjective π)
    (h3 : (3 : k) ≠ 0)
    (E : WeierstrassCurve (PowerSeries 𝒪)) [E.IsElliptic]
    (hj : PowerSeries.map π E.j ≠
      PowerSeries.C (PowerSeries.constantCoeff (PowerSeries.map π E.j)))
    {n : ℕ} (hm : ((2 * n + 1 : ℕ) : k) ≠ 0) (hsq : ¬ IsSquare (2 * n + 1))
    (Q₀ : (E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).toAffine.Point)
    (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    {h : Polynomial (PowerSeries 𝒪)} (hh : h.Monic) (hdvd : h ∣ E.preΨ' (2 * n + 1))
    (hmap : h.map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) =
      WeierstrassCurve.kernelPolynomial
        ((E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).oddOrderSummingSet Q₀ n))
    [(E.kohelQuotient h).IsElliptic]
    {x₁ y₁ x₂ : PowerSeries 𝒪} (hP₁ : E.toAffine.Equation x₁ y₁)
    (hx₁ : E.Ψ₃.eval x₁ = 0) (hx₂ : E.Ψ₃.eval x₂ = 0)
    (hA₃ : IsUnit (E.deuringA₃ x₁ y₁)) (hx : PowerSeries.map π (x₂ - x₁) ≠ 0)
    {x₁' y₁' x₂' : PowerSeries 𝒪} (hP₁' : (E.kohelQuotient h).toAffine.Equation x₁' y₁')
    (hx₁' : (E.kohelQuotient h).Ψ₃.eval x₁' = 0) (hx₂' : (E.kohelQuotient h).Ψ₃.eval x₂' = 0)
    (hA₃' : IsUnit ((E.kohelQuotient h).deuringA₃ x₁' y₁'))
    (hx' : PowerSeries.map π (x₂' - x₁') ≠ 0) :
    PowerSeries.map π ((E.kohelQuotient h).levelThreeModulus x₁' y₁' x₂'
      - E.levelThreeModulus x₁ y₁ x₂) ≠ 0 :=
  LevelThreeDisc.main π hπ h3 E hj hm hsq Q₀ hQ₀ hh hdvd hmap hP₁ hx₁ hx₂ hA₃ hx hP₁' hx₁' hx₂'
    hA₃' hx'

end S_WeierstrassCurve_map_levelThreeModulus_kohelQuotient_sub_ne_zero_of_map_j_ne_C
end P2MW
export P2MW.S_WeierstrassCurve_map_levelThreeModulus_kohelQuotient_sub_ne_zero_of_map_j_ne_C (solution)
