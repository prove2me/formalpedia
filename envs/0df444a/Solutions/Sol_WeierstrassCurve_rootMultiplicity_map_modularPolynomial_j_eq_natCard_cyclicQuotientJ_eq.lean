-- Prove2me | solution 1 for WeierstrassCurve.rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b24ee770-fb90-587d-b994-0ad839f8d974

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Theorems.Thm_WeierstrassCurve_map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix"
p2m_attr_erase "simp" "ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"

set_option autoImplicit false

universe u

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_map map toAffine j cyclicQuotientJ map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ"
namespace ModPolyRootMult
p2m_open "WeierstrassCurve"

open Polynomial

section General

variable {L : Type u} [Field L]

theorem X_sub_C_ne_one' (a : L) : (X - C a : L[X]) ≠ 1 := by
  intro h
  have := congrArg natDegree h
  rw [natDegree_X_sub_C, natDegree_one] at this
  exact one_ne_zero this

theorem finite_of_eq_finprod {ι : Type*} {S : Set ι} (f : ι → L) {p : L[X]} (hp : p ≠ 1)
    (h : p = ∏ᶠ i ∈ S, (X - C (f i))) : S.Finite := by
  by_contra hS
  apply hp
  rw [h]
  apply finprod_mem_eq_one_of_infinite
  have hsupp : S ∩ Function.mulSupport (fun i => X - C (f i)) = S := by
    apply Set.inter_eq_left.mpr
    intro i _
    rw [Function.mem_mulSupport]
    exact X_sub_C_ne_one' (f i)
  rw [hsupp]
  exact hS

theorem rootMultiplicity_finprod_X_sub_C [DecidableEq L] {ι : Type*} {S : Set ι} (hS : S.Finite)
    (f : ι → L) (y : L) :
    (∏ᶠ i ∈ S, (X - C (f i))).rootMultiplicity y = Nat.card {i // i ∈ S ∧ f i = y} := by
  classical
  rw [finprod_mem_eq_finite_toFinset_prod _ hS]
  have hprod : ∏ i ∈ hS.toFinset, (X - C (f i)) =
      ((hS.toFinset.val.map f).map fun a => X - C a).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  rw [hprod, ← count_roots, roots_multiset_prod_X_sub_C, Multiset.count_map]
  have hfin : {i | i ∈ S ∧ f i = y}.Finite := hS.subset fun i hi => hi.1
  have h1 : (Multiset.filter (fun a => y = f a) hS.toFinset.val) = hfin.toFinset.val := by
    rw [← Finset.filter_val]
    congr 1
    ext i
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hi, hy⟩; exact ⟨hi, hy.symm⟩
    · rintro ⟨hi, hy⟩; exact ⟨hi, hy.symm⟩
  rw [h1, ← Finset.card_def, ← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq]
  rfl

end General

section Curve

open ModularCurve

variable (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
  (L : Type u) [Field L] [DecidableEq L] [IsAlgClosed L] (hN : (N : L) ≠ 0)
  (E : WeierstrassCurve L) [E.IsElliptic]

theorem dedekindPsi_ne_zero : dedekindPsi N ≠ 0 := by
  have hN : N ≠ 0 := NeZero.ne N
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hN, squarefree_one⟩
  have hle : N / 1 ≤ dedekindPsi N :=
    Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1
  rw [Nat.div_one] at hle
  omega

omit [DecidableEq L] [IsAlgClosed L] in

theorem fibrePoly_ne_one :
    data.Φ.map (eval₂RingHom (Int.castRingHom L) E.j) ≠ 1 := by
  intro h
  have hdeg := congrArg natDegree h
  rw [data.monic.natDegree_map, data.natDegree_eq, natDegree_one] at hdeg
  exact dedekindPsi_ne_zero N hdeg

include data hN in

theorem finite_cycSub :
    {H : AddSubgroup E.toAffine.Point | IsAddCyclic H ∧ Nat.card H = N}.Finite :=
  finite_of_eq_finprod (fun H => E.cyclicQuotientJ H N) (fibrePoly_ne_one N data L E)
    (WeierstrassCurve.map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ N data L hN E)

include hN in

theorem main (y : L) :
    (data.Φ.map (eval₂RingHom (Int.castRingHom L) E.j)).rootMultiplicity y =
      Nat.card {H : AddSubgroup E.toAffine.Point //
        (IsAddCyclic H ∧ Nat.card H = N) ∧ E.cyclicQuotientJ H N = y} := by
  rw [WeierstrassCurve.map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ N data L hN E,
    rootMultiplicity_finprod_X_sub_C (finite_cycSub N data L hN E)]
  rfl

include hN in

theorem isRoot_iff_exists (y : L) :
    (data.Φ.map (eval₂RingHom (Int.castRingHom L) E.j)).IsRoot y ↔
      ∃ H : AddSubgroup E.toAffine.Point, (IsAddCyclic H ∧ Nat.card H = N) ∧ E.cyclicQuotientJ H N = y := by
  have hp0 : data.Φ.map (eval₂RingHom (Int.castRingHom L) E.j) ≠ 0 := (data.monic.map _).ne_zero
  haveI : Finite {H : AddSubgroup E.toAffine.Point //
      (IsAddCyclic H ∧ Nat.card H = N) ∧ E.cyclicQuotientJ H N = y} :=
    Set.finite_coe_iff.mpr ((finite_cycSub N data L hN E).subset fun H hH => hH.1)
  have h1 : (data.Φ.map (eval₂RingHom (Int.castRingHom L) E.j)).IsRoot y ↔
      0 < (data.Φ.map (eval₂RingHom (Int.castRingHom L) E.j)).rootMultiplicity y := by
    rw [rootMultiplicity_pos']
    exact ⟨fun h => ⟨hp0, h⟩, fun h => h.2⟩
  rw [h1, main N data L hN E y, Nat.pos_iff_ne_zero, Ne, Nat.card_eq_zero, not_or, not_isEmpty_iff,
    not_infinite_iff_finite]
  constructor
  · rintro ⟨⟨⟨H, hH⟩⟩, -⟩; exact ⟨H, hH⟩
  · rintro ⟨H, hH⟩; exact ⟨⟨⟨H, hH⟩⟩, inferInstance⟩

end Curve

end WeierstrassCurve.ModPolyRootMult

open ModularCurve _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq.WeierstrassCurve in

theorem solution
    (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (L : Type u) [Field L] [DecidableEq L] [IsAlgClosed L] (hN : (N : L) ≠ 0)
    (E : WeierstrassCurve L) [E.IsElliptic] (y : L) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom L) E.j)).rootMultiplicity y =
      Nat.card {H : AddSubgroup E.toAffine.Point //
        (IsAddCyclic H ∧ Nat.card H = N) ∧ E.cyclicQuotientJ H N = y} :=
  WeierstrassCurve.ModPolyRootMult.main N data L hN E y

end S_WeierstrassCurve_rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq
end P2MW
export P2MW.S_WeierstrassCurve_rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq (solution)
