-- Prove2me | solution 1 for WeierstrassCurve.cyclicQuotientJ_mem_range_algebraMap_of_forall_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ec472cc7-3d90-54cc-8d32-88f479d6e401

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_cyclicQuotientJ_mem_range_algebraMap_of_forall_map_eq
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.reducePoint_zero FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map map_j IsIntegral toAffine Affine.Point Affine.Point.map minimal baseChange j cyclicQuotientJ cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed"
p2m_open "WeierstrassCurve"
namespace CQJDescent

open Polynomial

section Galois

variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K]

theorem mem_range_algebraMap_of_forall_algEquiv [IsAlgClosed K] [Algebra.IsAlgebraic F K]
    {y : K} (hsep : _root_.IsSeparable F y) (hfix : ∀ σ : K ≃ₐ[F] K, σ y = y) :
    y ∈ (algebraMap F K).range := by
  haveI : IsAlgClosure F K := ⟨inferInstance, inferInstance⟩
  set p : F[X] := minpoly F y with hp
  have hint : _root_.IsIntegral F y := hsep.isIntegral
  have hp0 : p ≠ 0 := minpoly.ne_zero hint

  set M : IntermediateField F K := IntermediateField.adjoin F (p.rootSet K) with hM
  have hsplits : (p.map (algebraMap F K)).Splits := IsAlgClosed.splits _
  haveI hSF : p.IsSplittingField F M := IntermediateField.adjoin_rootSet_isSplittingField hsplits
  haveI : FiniteDimensional F M := Polynomial.IsSplittingField.finiteDimensional M p
  haveI : IsGalois F M := IsGalois.of_separable_splitting_field (p := p) hsep

  have hyroot : y ∈ p.rootSet K := by
    rw [Polynomial.mem_rootSet]
    exact ⟨hp0, minpoly.aeval F y⟩
  have hyM : y ∈ M := IntermediateField.subset_adjoin F (p.rootSet K) hyroot
  set ym : M := ⟨y, hyM⟩ with hym
  have hval : algebraMap M K ym = y := rfl

  have hfixM : ∀ τ : M ≃ₐ[F] M, τ ym = ym := by
    intro τ
    have h1 : (τ.liftNormal K) (algebraMap M K ym) = algebraMap M K (τ ym) :=
      τ.liftNormal_commutes K ym
    rw [hval, hfix] at h1
    exact (algebraMap M K).injective (h1.symm.trans hval.symm)
  have hbot : ym ∈ (⊥ : IntermediateField F M) := (IsGalois.mem_bot_iff_fixed ym).mpr hfixM
  rw [IntermediateField.mem_bot] at hbot
  obtain ⟨a, ha⟩ := hbot
  refine ⟨a, ?_⟩
  have : algebraMap M K (algebraMap F M a) = algebraMap M K ym := by rw [ha]
  rw [← IsScalarTower.algebraMap_apply] at this
  rw [this, hval]

end Galois

section Finite

variable {F : Type*} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]
variable (K : Type*) [Field K] [DecidableEq K] [IsAlgClosed K] [Algebra F K]

theorem finite_addSubgroup_card_eq (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    Finite {H : AddSubgroup (E.baseChange K).toAffine.Point // Nat.card H = N} := by
  obtain ⟨eT⟩ := nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := K) E (n := N) hN

  haveI : Finite (Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point N) :=
    Finite.of_equiv _ eT.toEquiv

  let ι : {H : AddSubgroup (E.baseChange K).toAffine.Point // Nat.card H = N} →
      Set (Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point N) :=
    fun H => {P | (P : (E.baseChange K).toAffine.Point) ∈ H.1}
  refine Finite.of_injective ι fun H₁ H₂ h => ?_
  have hmem : ∀ (H : {H : AddSubgroup (E.baseChange K).toAffine.Point // Nat.card H = N})
      (P : (E.baseChange K).toAffine.Point), P ∈ H.1 →
        P ∈ Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point N := by
    intro H P hP
    haveI : Finite H.1 := Nat.finite_of_card_ne_zero (by rw [H.2]; exact NeZero.ne N)
    rw [Submodule.mem_torsionBy_iff]
    have h1 : addOrderOf (⟨P, hP⟩ : H.1) ∣ N := by
      have := addOrderOf_dvd_natCard (⟨P, hP⟩ : H.1)
      rwa [H.2] at this
    have h2 : N • (⟨P, hP⟩ : H.1) = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp h1
    have h3 : N • P = 0 := by
      have := congrArg Subtype.val h2
      simpa using this
    simpa using h3
  apply Subtype.ext
  ext P
  constructor
  · intro hP
    have : (⟨P, hmem H₁ P hP⟩ : Submodule.torsionBy ℤ _ N) ∈ ι H₁ := hP
    rw [h] at this
    exact this
  · intro hP
    have : (⟨P, hmem H₂ P hP⟩ : Submodule.torsionBy ℤ _ N) ∈ ι H₂ := hP
    rw [← h] at this
    exact this

end Finite

section Main

variable {F : Type*} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]
variable (K : Type*) [Field K] [DecidableEq K] [IsAlgClosed K] [Algebra F K]

scoped instance isElliptic_baseChange : (E.baseChange K).IsElliptic :=
  inferInstanceAs ((E.map (algebraMap F K)).IsElliptic)

omit [DecidableEq K] [IsAlgClosed K] in
theorem baseChange_j : (E.baseChange K).j = algebraMap F K E.j := E.map_j (algebraMap F K)

omit [DecidableEq K] [IsAlgClosed K] in

theorem map_fibrePoly (Φ : Polynomial (Polynomial ℤ)) :
    (Φ.map (eval₂RingHom (Int.castRingHom F) E.j)).map (algebraMap F K) =
      Φ.map (eval₂RingHom (Int.castRingHom K) (algebraMap F K E.j)) := by
  rw [Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext (fun n => ?_) ?_
  · simp
  · simp

theorem main [Algebra.IsAlgebraic F K]
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N) (hN : (N : K) ≠ 0)
    (hsep : (data.Φ.map (eval₂RingHom (Int.castRingHom K) (algebraMap F K E.j))).Separable)
    (H : AddSubgroup (E.baseChange K).toAffine.Point) (hH : IsAddCyclic H ∧ Nat.card H = N)
    (hstab : ∀ σ : K ≃ₐ[F] K, H.map (WeierstrassCurve.Affine.Point.map (σ : K →ₐ[F] K)) = H) :
    (E.baseChange K).cyclicQuotientJ H N ∈ (algebraMap F K).range := by
  set y := (E.baseChange K).cyclicQuotientJ H N with hy

  have hmult := rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq N data K hN
    (E.baseChange K) y
  have hcard_ne : Nat.card {H' : AddSubgroup (E.baseChange K).toAffine.Point //
      (IsAddCyclic H' ∧ Nat.card H' = N) ∧ (E.baseChange K).cyclicQuotientJ H' N = y} ≠ 0 := by
    haveI := finite_addSubgroup_card_eq E K N hN
    haveI : Finite {H' : AddSubgroup (E.baseChange K).toAffine.Point //
        (IsAddCyclic H' ∧ Nat.card H' = N) ∧ (E.baseChange K).cyclicQuotientJ H' N = y} :=
      Finite.of_injective
        (fun H' => (⟨H'.1, H'.2.1.2⟩ : {H : AddSubgroup (E.baseChange K).toAffine.Point //
          Nat.card H = N})) (fun a b h => Subtype.ext (congrArg (fun z => z.1) h :))
    haveI : Nonempty {H' : AddSubgroup (E.baseChange K).toAffine.Point //
        (IsAddCyclic H' ∧ Nat.card H' = N) ∧ (E.baseChange K).cyclicQuotientJ H' N = y} :=
      ⟨⟨H, hH, rfl⟩⟩
    exact Nat.card_pos.ne'
  have hroot : ((data.Φ.map (eval₂RingHom (Int.castRingHom K) (E.baseChange K).j))).IsRoot y := by
    by_contra h
    exact hcard_ne (hmult ▸ rootMultiplicity_eq_zero h)
  rw [baseChange_j] at hroot

  set p₀ : F[X] := data.Φ.map (eval₂RingHom (Int.castRingHom F) E.j) with hp₀
  have hp₀map : p₀.map (algebraMap F K) =
      data.Φ.map (eval₂RingHom (Int.castRingHom K) (algebraMap F K E.j)) := map_fibrePoly E K data.Φ
  have hp₀sep : p₀.Separable := by
    rw [← Polynomial.separable_map (algebraMap F K), hp₀map]
    exact hsep
  have haeval : aeval y p₀ = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hp₀map]
    exact hroot
  have hysep : _root_.IsSeparable F y :=
    Polynomial.Separable.of_dvd hp₀sep (minpoly.dvd F y haeval)

  have hfix : ∀ σ : K ≃ₐ[F] K, σ y = y := by
    intro σ
    have h := cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed E (σ : K →ₐ[F] K) H N
    rw [hstab σ] at h

    exact (h.trans rfl).symm

  exact mem_range_algebraMap_of_forall_algEquiv hysep hfix

end Main

end CQJDescent
p2m_reactivate "P2MW.S_WeierstrassCurve_cyclicQuotientJ_mem_range_algebraMap_of_forall_map_eq.WeierstrassCurve.CQJDescent"
end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_cyclicQuotientJ_mem_range_algebraMap_of_forall_map_eq.WeierstrassCurve.CQJDescent P2MW.S_WeierstrassCurve_cyclicQuotientJ_mem_range_algebraMap_of_forall_map_eq.WeierstrassCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_cyclicQuotientJ_mem_range_algebraMap_of_forall_map_eq.WeierstrassCurve.CQJDescent P2MW.S_WeierstrassCurve_cyclicQuotientJ_mem_range_algebraMap_of_forall_map_eq.WeierstrassCurve"

universe u v in

theorem solution
    {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]
    (K : Type v) [Field K] [DecidableEq K] [IsAlgClosed K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N) (hN : (N : K) ≠ 0)
    (hsep : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K)
      (algebraMap F K E.j))).Separable)
    (H : AddSubgroup (E.baseChange K).toAffine.Point) (hH : IsAddCyclic H ∧ Nat.card H = N)
    (hstab : ∀ σ : K ≃ₐ[F] K,
      H.map (WeierstrassCurve.Affine.Point.map (σ : K →ₐ[F] K)) = H) :
    (E.baseChange K).cyclicQuotientJ H N ∈ (algebraMap F K).range :=
  WeierstrassCurve.CQJDescent.main E K N data hN hsep H hH hstab

end S_WeierstrassCurve_cyclicQuotientJ_mem_range_algebraMap_of_forall_map_eq
end P2MW
export P2MW.S_WeierstrassCurve_cyclicQuotientJ_mem_range_algebraMap_of_forall_map_eq (solution)
