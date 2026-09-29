-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_algebraMap_eq_cyclicQuotientJ_of_raw_rigidDataPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1333dca4-edb5-5a89-ab54-9942f0196093

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_IsGamma0PowAt_zmultiples_eq_zmultiples_of_isRoot_of_addOrderOf_eq
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_eval2RingHom_j_of_transcendental
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_mem_range_algebraMap_of_forall_map_eq
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_algebraMap_eq_cyclicQuotientJ_of_raw_rigidDataPow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"

set_option autoImplicit false
open ModularCurve WeierstrassCurve.DrinfeldGlobal

set_option maxHeartbeats 6400000 in
theorem solution
    (A : Type) [CommRing A] (ℓ M' q : ℕ) [NeZero M']
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q)
    (𝕂 : Type) [Field 𝕂] [CharZero 𝕂] [Algebra A 𝕂]
    (x : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw 𝕂)
    (hjt : Transcendental ℚ (x.curve.c₄ ^ 3 / x.curve.Δ))
    (Ω : Type) [Field Ω] [DecidableEq Ω] [IsAlgClosed Ω] [Algebra 𝕂 Ω] [Algebra.IsAlgebraic 𝕂 Ω]
    (d : ℕ) [NeZero d] (hd : d ∣ M') :
    ∃ J : 𝕂, ∀ (g : (x.curve.baseChange Ω).toAffine.Point),
      (addOrderOf g = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Ω) (h₁ : (x.curve.baseChange Ω).toAffine.Nonsingular x₁ y₁),
          n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          ((x.level.1 p).map (algebraMap 𝕂 Ω)).IsRoot x₁) →
      algebraMap 𝕂 Ω J = (x.curve.baseChange Ω).cyclicQuotientJ (AddSubgroup.zmultiples ((M' / d) • g)) d := by
  classical
  haveI hE : x.curve.IsElliptic := ⟨x.isUnit_Δ⟩

  set E := x.curve with hEdef
  have hlev : ∀ p : ↥M'.primeFactors,
      ModularCurve.IsGamma0PowAt (E.baseChange Ω) (p : ℕ) (M'.factorization (p : ℕ))
        ((x.level.1 p).map (algebraMap 𝕂 Ω)) := by
    intro p
    have h0 := x.isLevel.1 p
    exact ModularCurve.IsGamma0PowAt.map (algebraMap 𝕂 Ω) _ _ _ h0

  let Cut : (E.baseChange Ω).toAffine.Point → Prop := fun g =>
    addOrderOf g = M' ∧
      ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Ω) (h₁ : (E.baseChange Ω).toAffine.Nonsingular x₁ y₁),
        n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
        ((x.level.1 p).map (algebraMap 𝕂 Ω)).IsRoot x₁
  have hM'0 : (M' : ℕ) ≠ 0 := NeZero.ne M'
  haveI hΩ0' : CharZero Ω := charZero_of_injective_algebraMap (algebraMap 𝕂 Ω).injective
  haveI hEΩ' : (E.baseChange Ω).IsElliptic := by unfold WeierstrassCurve.baseChange; infer_instance

  have keyP : ∀ g g' : (E.baseChange Ω).toAffine.Point, Cut g → Cut g' → ∀ p : ↥M'.primeFactors,
      AddSubgroup.zmultiples ((M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g) =
        AddSubgroup.zmultiples ((M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g') := by
    intro g g' hg hg' p
    have hpp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    haveI : Fact (p : ℕ).Prime := ⟨hpp⟩
    have hpk : (p : ℕ) ^ M'.factorization (p : ℕ) ∣ M' := Nat.ordProj_dvd M' p
    have hn0 : M' / (p : ℕ) ^ M'.factorization (p : ℕ) ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM'0) hpk) (Nat.pos_of_ne_zero (pow_ne_zero _ hpp.ne_zero))).ne'
    have hord : ∀ g₁ : (E.baseChange Ω).toAffine.Point, Cut g₁ →
        addOrderOf ((M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g₁) = (p : ℕ) ^ M'.factorization (p : ℕ) := by
      intro g₁ hg₁
      rw [addOrderOf_nsmul' g₁ hn0, hg₁.1, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpk), Nat.div_div_self hpk hM'0]
    have hk1 : 1 < (p : ℕ) ^ M'.factorization (p : ℕ) := by
      apply Nat.one_lt_pow _ hpp.one_lt
      exact (Nat.Prime.factorization_pos_of_dvd hpp hM'0 (Nat.dvd_of_mem_primeFactors p.2)).ne'
    have hpΩ : ((p : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero

    cases hc : (M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g with
    | zero =>
      exfalso; have h1 := hord g hg; rw [hc, show (WeierstrassCurve.Affine.Point.zero : (E.baseChange Ω).toAffine.Point) = 0 from rfl, addOrderOf_zero] at h1; omega
    | some x₁ y₁ h₁ =>
      cases hc' : (M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g' with
      | zero =>
        exfalso; have h1 := hord g' hg'; rw [hc', show (WeierstrassCurve.Affine.Point.zero : (E.baseChange Ω).toAffine.Point) = 0 from rfl, addOrderOf_zero] at h1; omega
      | some x₂ y₂ h₂ =>
        have hr₁ := hg.2 p _ x₁ y₁ h₁ hc (hord g hg)
        have hr₂ := hg'.2 p _ x₂ y₂ h₂ hc' (hord g' hg')
        have ho₁ : addOrderOf (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = (p : ℕ) ^ M'.factorization (p : ℕ) := by
          rw [← hc]; exact hord g hg
        have ho₂ : addOrderOf (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = (p : ℕ) ^ M'.factorization (p : ℕ) := by
          rw [← hc']; exact hord g' hg'
        exact ModularCurve.IsGamma0PowAt.zmultiples_eq_zmultiples_of_isRoot_of_addOrderOf_eq
          (E.baseChange Ω) (p : ℕ) (M'.factorization (p : ℕ)) hpΩ _ (hlev p) x₁ y₁ x₂ y₂ h₁ h₂ ho₁ ho₂ hr₁ hr₂

  have keyA : ∀ g g' : (E.baseChange Ω).toAffine.Point, Cut g → Cut g' →
      AddSubgroup.zmultiples g = AddSubgroup.zmultiples g' := by
    suffices hsuff : ∀ g g' : (E.baseChange Ω).toAffine.Point, Cut g → Cut g' →
        AddSubgroup.zmultiples g ≤ AddSubgroup.zmultiples g' by
      intro g g' hg hg'; exact le_antisymm (hsuff g g' hg hg') (hsuff g' g hg' hg)
    intro g g' hg hg'
    set T : AddSubgroup (E.baseChange Ω).toAffine.Point := AddSubgroup.zmultiples g ⊓ AddSubgroup.zmultiples g' with hT
    have hcardg : Nat.card (AddSubgroup.zmultiples g) = M' := by rw [Nat.card_zmultiples, hg.1]
    haveI hfin : Finite (AddSubgroup.zmultiples g) := Nat.finite_of_card_ne_zero (hcardg ▸ hM'0)
    have hTle : T ≤ AddSubgroup.zmultiples g := inf_le_left

    have hdvd : M' ∣ Nat.card T := by
      rw [Nat.dvd_iff_prime_pow_dvd_dvd]
      intro r j hr hrj
      by_cases hj : j = 0
      · simp [hj]
      have hrM : r ∣ M' := (dvd_pow_self r hj).trans hrj
      have hrmem : r ∈ M'.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hrM, hM'0⟩
      have hjle : j ≤ M'.factorization r := (Nat.Prime.pow_dvd_iff_le_factorization hr hM'0).mp hrj
      have hsub : AddSubgroup.zmultiples ((M' / r ^ M'.factorization r) • g) ≤ T := by
        rw [hT]; refine le_inf ?_ ?_
        · exact AddSubgroup.zmultiples_le_of_mem ((AddSubgroup.zmultiples g).nsmul_mem (AddSubgroup.mem_zmultiples g) _)
        · rw [keyP g g' hg hg' ⟨r, hrmem⟩]
          exact AddSubgroup.zmultiples_le_of_mem ((AddSubgroup.zmultiples g').nsmul_mem (AddSubgroup.mem_zmultiples g') _)
      have hcardC : Nat.card (AddSubgroup.zmultiples ((M' / r ^ M'.factorization r) • g)) = r ^ M'.factorization r := by
        have hpk : r ^ M'.factorization r ∣ M' := Nat.ordProj_dvd M' r
        have hn0 : M' / r ^ M'.factorization r ≠ 0 :=
          (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM'0) hpk) (Nat.pos_of_ne_zero (pow_ne_zero _ hr.ne_zero))).ne'
        rw [Nat.card_zmultiples, addOrderOf_nsmul' g hn0, hg.1, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpk),
          Nat.div_div_self hpk hM'0]
      exact (pow_dvd_pow r hjle).trans (hcardC ▸ AddSubgroup.card_dvd_of_le hsub)
    have hTdvd : Nat.card T ∣ M' := hcardg ▸ AddSubgroup.card_dvd_of_le hTle
    have hTcard : Nat.card (AddSubgroup.zmultiples g) ≤ Nat.card T := by
      rw [hcardg, Nat.dvd_antisymm hTdvd hdvd]
    have hTeq : T = AddSubgroup.zmultiples g := AddSubgroup.eq_of_le_of_card_ge hTle hTcard
    calc AddSubgroup.zmultiples g = T := hTeq.symm
      _ ≤ AddSubgroup.zmultiples g' := inf_le_right

  have keyA' : ∀ g g' : (E.baseChange Ω).toAffine.Point, Cut g → Cut g' →
      AddSubgroup.zmultiples ((M' / d) • g) = AddSubgroup.zmultiples ((M' / d) • g') := by
    intro g g' hg hg'
    have h := keyA g g' hg hg'
    apply le_antisymm
    · rw [AddSubgroup.zmultiples_le]
      have hm : g ∈ AddSubgroup.zmultiples g' := h ▸ AddSubgroup.mem_zmultiples g
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
      refine AddSubgroup.mem_zmultiples_iff.mpr ⟨m, ?_⟩
      rw [← hm, smul_comm]
    · have hm : g' ∈ AddSubgroup.zmultiples g := h.symm ▸ AddSubgroup.mem_zmultiples g'
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
      rw [AddSubgroup.zmultiples_le]
      refine AddSubgroup.mem_zmultiples_iff.mpr ⟨m, ?_⟩
      rw [← hm, smul_comm]

  have keyB : ∀ (σ : Ω ≃ₐ[𝕂] Ω) (g : (E.baseChange Ω).toAffine.Point), Cut g →
      Cut (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[𝕂] Ω) g) := by
    intro σ g hg
    have hinj : Function.Injective (WeierstrassCurve.Affine.Point.map (W' := E) (σ : Ω →ₐ[𝕂] Ω)) :=
      WeierstrassCurve.Affine.Point.map_injective _
    refine ⟨?_, ?_⟩
    · rw [addOrderOf_injective _ hinj g]; exact hg.1
    · intro p n x₁ y₁ h₁ hn hord
      have hng : WeierstrassCurve.Affine.Point.map (W' := E) (σ : Ω →ₐ[𝕂] Ω) (n • g) =
          WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ := by rw [map_nsmul]; exact hn
      have hord' : addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) := by
        rw [← addOrderOf_injective _ hinj (n • g), map_nsmul]; exact hord
      cases hc : n • g with
      | zero =>
        rw [hc, show (WeierstrassCurve.Affine.Point.zero : (E.baseChange Ω).toAffine.Point) = 0 from rfl, map_zero] at hng
        exact absurd hng (fun h0 => by cases h0)
      | some x₁' y₁' h₁' =>
        rw [hc, WeierstrassCurve.Affine.Point.map_some] at hng
        have hx : (σ : Ω →ₐ[𝕂] Ω) x₁' = x₁ := (WeierstrassCurve.Affine.Point.some.inj hng).1
        have hr := hg.2 p n x₁' y₁' h₁' hc hord'
        have hr2 := Polynomial.IsRoot.map (f := ((σ : Ω →ₐ[𝕂] Ω) : Ω →+* Ω)) hr
        rw [Polynomial.map_map, AlgHom.comp_algebraMap] at hr2
        rw [← hx]; exact hr2
  by_cases hex : ∃ g, Cut g
  · obtain ⟨g₀, hg₀⟩ := hex
    set H : AddSubgroup (E.baseChange Ω).toAffine.Point := AddSubgroup.zmultiples ((M' / d) • g₀) with hH

    have hd0 : (d : ℕ) ≠ 0 := NeZero.ne d
    have hcard : IsAddCyclic H ∧ Nat.card H = d := by
      refine ⟨?_, ?_⟩
      · rw [hH]; exact AddSubgroup.isAddCyclic_zmultiples _
      · have hne : M' / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM'0) hd) (Nat.pos_of_ne_zero hd0)).ne'
        rw [hH, Nat.card_zmultiples, addOrderOf_nsmul' g₀ hne, hg₀.1, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd),
          Nat.div_div_self hd hM'0]

    have hstab : ∀ σ : Ω ≃ₐ[𝕂] Ω,
        H.map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[𝕂] Ω)) = H := by
      intro σ
      rw [hH, AddMonoidHom.map_zmultiples, map_nsmul]
      exact (keyA' _ _ (keyB σ g₀ hg₀) hg₀)

    obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData d
    have hdΩ : ((d : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hd0
    have hjΩ : (E.baseChange Ω).j = algebraMap 𝕂 Ω E.j := E.map_j (algebraMap 𝕂 Ω)
    have hjt' : Transcendental ℚ (E.baseChange Ω).j := by
      have hjE : E.j = E.c₄ ^ 3 / E.Δ := by
        rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', inv_mul_eq_div]
      rw [hjΩ, hjE]
      exact (transcendental_algebraMap_iff (algebraMap 𝕂 Ω).injective).mpr hjt
    have hsep := ModularCurve.ModularPolynomialData.separable_map_eval2RingHom_j_of_transcendental
      ℚ d data Ω hdΩ (E.baseChange Ω) hjt'
    rw [hjΩ] at hsep
    obtain ⟨J, hJ⟩ := WeierstrassCurve.cyclicQuotientJ_mem_range_algebraMap_of_forall_map_eq
      E Ω d data hdΩ hsep H hcard hstab
    refine ⟨J, fun g hg => ?_⟩
    rw [hJ, hH, keyA' g₀ g hg₀ hg]
  · refine ⟨0, fun g hg => ?_⟩
    exact absurd ⟨g, hg⟩ hex

end S_WeierstrassCurve_DrinfeldGlobal_exists_algebraMap_eq_cyclicQuotientJ_of_raw_rigidDataPow
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_algebraMap_eq_cyclicQuotientJ_of_raw_rigidDataPow (solution)
