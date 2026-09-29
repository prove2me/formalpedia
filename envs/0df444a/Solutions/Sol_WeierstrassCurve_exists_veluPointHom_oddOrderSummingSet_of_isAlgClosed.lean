-- Prove2me | solution 1 for WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3e9eeb7e-cd38-571f-90c0-50194032adb5

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_WeierstrassCurve_GenusOnePic0
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Theorems.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem
import Theorems.Thm_Algebra_IsSeparable_of_coprime_finrank_expChar
import Theorems.Thm_AlgebraicCurve_normFormulaAlong_of_separableAlong
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_hasPrincipalDivisors_functionField_of_isElliptic
import Theorems.Thm_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point AlgebraicCurve

universe u

noncomputable section

namespace P2MA6

variable {F : Type u} [Field F] [DecidableEq F]
variable {V W : Affine F} [GenusOnePlaceGate V] [AbelTheorem V] [GenusOnePlaceGate W] [AbelTheorem W]
variable (ι : V.FunctionField →ₐ[F] W.FunctionField) (hι : ι.toRingHom.IsIntegral)

omit [DecidableEq F] [AbelTheorem V] [AbelTheorem W] in

theorem inertiaDegAlong_eq_one' (w : AlgebraicCurve.Place F W.FunctionField) :
    w.inertiaDegAlong ι hι = 1 := by
  have h := AlgebraicCurve.Place.deg_restrictAlong_mul_inertiaDegAlong ι hι w
  rw [GenusOnePlaceGate.deg_eq_one (W := V) (w.restrictAlong ι hι),
    GenusOnePlaceGate.deg_eq_one (W := W) w, one_mul] at h
  exact h

omit [DecidableEq F] [AbelTheorem V] [AbelTheorem W] in
theorem pushforwardAlong_single_eq' (w : AlgebraicCurve.Place F W.FunctionField) (n : ℤ) :
    Divisor.pushforwardAlong ι hι (Finsupp.single w n) = Finsupp.single (w.restrictAlong ι hι) n := by
  rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one' ι hι w, Nat.cast_one, mul_one]

variable (hfin : FiniteAlong F ι) (hN : NormFormulaAlong F ι hfin)

omit [AbelTheorem V] [AbelTheorem W] in
theorem pushforwardAlongDegZero_pointDivisor' {P : W.Point} {Q : V.Point}
    (hP : (placeOfPoint P).restrictAlong ι hι = placeOfPoint Q)
    (h0 : (placeOfPoint (0 : W.Point)).restrictAlong ι hι = placeOfPoint (0 : V.Point)) :
    Pic0.pushforwardAlongDegZero ι hι (pointDivisor P) = pointDivisor Q := by
  refine Subtype.ext ?_
  rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, coe_pointDivisor, map_sub,
    pushforwardAlong_single_eq' ι hι, pushforwardAlong_single_eq' ι hι, hP, h0]

omit [AbelTheorem V] [AbelTheorem W] in
theorem pushforwardAlongHom_pointClass' {P : W.Point} {Q : V.Point}
    (hP : (placeOfPoint P).restrictAlong ι hι = placeOfPoint Q)
    (h0 : (placeOfPoint (0 : W.Point)).restrictAlong ι hι = placeOfPoint (0 : V.Point)) :
    Pic0.pushforwardAlongHom ι hι hfin hN (pointClass P) = pointClass Q := by
  show Pic0.pushforwardAlongHom ι hι hfin hN (Pic0.mk (pointDivisor P)) = Pic0.mk (pointDivisor Q)
  rw [Pic0.pushforwardAlongHom_mk, pushforwardAlongDegZero_pointDivisor' ι hι hP h0]

theorem pointMapOfPushforward_apply' (P : W.Point) :
    pointMapOfPushforward ι hι hfin hN P
      = genusOnePic0Equiv V (Pic0.pushforwardAlongHom ι hι hfin hN (pointClass P)) := by
  rw [← genusOnePic0Equiv_symm_apply]
  rfl

theorem pointMapOfPushforward_eq_of_seam' (g : W.Point → V.Point) (hg0 : g 0 = 0)
    (hg : ∀ P, (placeOfPoint P).restrictAlong ι hι = placeOfPoint (g P)) (P : W.Point) :
    pointMapOfPushforward ι hι hfin hN P = g P := by
  rw [pointMapOfPushforward_apply',
    pushforwardAlongHom_pointClass' ι hι hfin hN (hg P) ((hg 0).trans (by rw [hg0])),
    genusOnePic0Equiv_apply, pic0ToPoint_pointClass]

end P2MA6

end

open P2MA6 in
theorem solution
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0)
    (Q : W.toAffine.Point) (hQord : addOrderOf Q = p) :
    let S := W.oddOrderSummingSet Q (p / 2)
    ∃ φ : W.toAffine.Point →+ (W.veluQuotient S).toAffine.Point,
      φ.ker = AddSubgroup.zmultiples Q ∧
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
        (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
          ∃ h', φ (.some x y h) = .some (W.veluX S x) (W.veluY S x y) h') := by
  intro S
  classical
  have hodd : p = 2 * (p / 2) + 1 := by
    rcases hp.eq_two_or_odd' with h | ⟨k, hk⟩
    · exact absurd h hp2
    · omega
  have hord : addOrderOf Q = 2 * (p / 2) + 1 := hQord.trans hodd
  have hnF : ((2 * (p / 2) + 1 : ℕ) : F) ≠ 0 := by rw [← hodd]; exact hpF
  have hΔ' : (W.veluQuotient S).Δ ≠ 0 :=
    veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq W (p / 2) Q hord
  haveI hVell : (W.veluQuotient S).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
  haveI : (W.veluQuotient S).toAffine.IsElliptic := hVell
  haveI : W.toAffine.IsElliptic := ‹W.IsElliptic›

  haveI : IsDedekindDomain W.toAffine.CoordinateRing := CoordinateRing.isDedekindDomain W
  haveI : IsDedekindDomain (W.veluQuotient S).toAffine.CoordinateRing :=
    CoordinateRing.isDedekindDomain (W.veluQuotient S)
  haveI : HasPrincipalDivisors F W.toAffine.FunctionField :=
    WeierstrassCurve.hasPrincipalDivisors_functionField_of_isElliptic W
  haveI : HasPrincipalDivisors F (W.veluQuotient S).toAffine.FunctionField :=
    WeierstrassCurve.hasPrincipalDivisors_functionField_of_isElliptic (W.veluQuotient S)
  obtain ⟨gW, cW, aW⟩ := exists_genusOnePlaceGate_isCentred_and_abelTheorem (W := W.toAffine)
  obtain ⟨gV, cV, aV⟩ :=
    exists_genusOnePlaceGate_isCentred_and_abelTheorem (W := (W.veluQuotient S).toAffine)
  letI : GenusOnePlaceGate W.toAffine := gW
  haveI : GenusOnePlaceGate.IsCentred W.toAffine := cW
  haveI : AbelTheorem W.toAffine := aW
  letI : GenusOnePlaceGate (W.veluQuotient S).toAffine := gV
  haveI : GenusOnePlaceGate.IsCentred (W.veluQuotient S).toAffine := cV
  haveI : AbelTheorem (W.veluQuotient S).toAffine := aV

  obtain ⟨ι, hι, hfin, hdeg, hker, hzero, haff⟩ :=
    exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed (W := W) hord hΔ'

  have hsep : SeparableAlong F ι := by
    letI := algebraAlong ι
    haveI : Module.Finite (W.veluQuotient S).toAffine.FunctionField W.toAffine.FunctionField := hfin
    obtain ⟨q, hq⟩ := ExpChar.exists F
    haveI : ExpChar (W.veluQuotient S).toAffine.FunctionField q :=
      expChar_of_injective_algebraMap (algebraMap F _).injective q
    have hcop : Nat.Coprime (Module.finrank (W.veluQuotient S).toAffine.FunctionField W.toAffine.FunctionField) q := by
      have hfr : Module.finrank (W.veluQuotient S).toAffine.FunctionField W.toAffine.FunctionField = 2 * (p / 2) + 1 :=
        hdeg
      rw [hfr]
      rcases hq with _ | ⟨hqprime⟩
      · exact Nat.coprime_one_right _
      · refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hqprime).mpr fun hdvd => hnF ?_))
        exact (CharP.cast_eq_zero_iff F q _).mpr hdvd
    exact Algebra.IsSeparable.of_coprime_finrank_expChar _ _ q hcop

  have hN : NormFormulaAlong F ι hfin := normFormulaAlong_of_separableAlong ι hfin hsep

  let g : W.toAffine.Point → (W.veluQuotient S).toAffine.Point := fun P =>
    match P with
    | 0 => 0
    | .some a b hab =>
        if hm : (Point.some a b hab : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q then 0
        else .some _ _ (Classical.choose (haff a b hab hm))
  have hg0 : g 0 = 0 := rfl
  have hgseam : ∀ P : W.toAffine.Point, (placeOfPoint P).restrictAlong ι hι = placeOfPoint (g P) := by
    intro P
    cases P with
    | zero => exact hzero _ (AddSubgroup.zero_mem _)
    | some a b hab =>
        by_cases hm : (Point.some a b hab : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q
        · have : g (.some a b hab) = 0 := by simp only [g, dif_pos hm]
          rw [this]; exact hzero _ hm
        · have : g (.some a b hab) = .some _ _ (Classical.choose (haff a b hab hm)) := by
            simp only [g, dif_neg hm]
          rw [this]; exact Classical.choose_spec (haff a b hab hm)

  refine ⟨pointMapOfPushforward ι hι hfin hN, ?_, ?_⟩
  · ext P
    rw [AddMonoidHom.mem_ker, pointMapOfPushforward_eq_of_seam' ι hι hfin hN g hg0 hgseam P]
    cases P with
    | zero => exact ⟨fun _ => AddSubgroup.zero_mem _, fun _ => rfl⟩
    | some a b hab =>
        by_cases hm : (Point.some a b hab : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q
        · simp only [g, dif_pos hm]; exact ⟨fun _ => hm, fun _ => trivial⟩
        · simp only [g, dif_neg hm]
          exact ⟨fun h0 => (Point.some_ne_zero _ h0).elim, fun h0 => absurd h0 hm⟩
  · intro x y h hP
    obtain ⟨h', _⟩ := haff x y h hP
    refine ⟨h', ?_⟩
    rw [pointMapOfPushforward_eq_of_seam' ι hι hfin hN g hg0 hgseam (.some x y h)]
    simp only [g, dif_neg hP]
    rfl

end S_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed (solution)
