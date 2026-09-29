-- Prove2me | solution 1 for WeierstrassCurve.Generic.exists_algEquiv_inLine_of_eval_prePsi_eq_zero_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3902aa83-efa8-5554-b6fc-f7b97947d27c

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_WeierstrassCurve_Generic
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_WeierstrassCurve_exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j
import Theorems.Thm_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Generic_exists_algEquiv_inLine_of_eval_prePsi_eq_zero_of_ne_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"

set_option autoImplicit false

noncomputable section

open Polynomial

namespace P2MKcGenX0Irr

section HomEval

variable {R : Type*} [CommRing R]

def homEval (c d : R) (q : R[X]) (D : ℕ) : R :=
  ∑ a ∈ Finset.range (D + 1), q.coeff a * c ^ a * d ^ (D - a)

theorem map_homEval {S : Type*} [CommRing S] (f : R →+* S) (c d : R) (q : R[X]) (D : ℕ) :
    f (homEval c d q D) = homEval (f c) (f d) (q.map f) D := by
  simp [homEval, map_sum, Polynomial.coeff_map]

theorem homEval_one_zero (c d : R) : homEval c d 1 0 = 1 := by
  simp [homEval]

theorem homEval_eq_pow_mul_eval {F : Type*} [Field F] (c d : F) (hd : d ≠ 0) (q : F[X]) {D : ℕ}
    (hq : q.natDegree ≤ D) : homEval c d q D = d ^ D * q.eval (c / d) := by
  rw [homEval, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hq), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hda : d ^ a ≠ 0 := pow_ne_zero _ hd
  rw [← pow_sub_mul_pow d ha', div_pow]
  field_simp

end HomEval

section Scaled

variable {R : Type*} [CommRing R]

def xDegBound (Φ : Polynomial (Polynomial ℤ)) : ℕ :=
  Φ.support.sup fun b => (Φ.coeff b).natDegree

theorem natDegree_coeff_le_xDegBound (Φ : Polynomial (Polynomial ℤ)) (b : ℕ) :
    (Φ.coeff b).natDegree ≤ xDegBound Φ := by
  by_cases hb : b ∈ Φ.support
  · exact Finset.le_sup (f := fun b => (Φ.coeff b).natDegree) hb
  · rw [Polynomial.notMem_support_iff.mp hb, natDegree_zero]
    exact Nat.zero_le _

def scaledPhi (Φ : Polynomial (Polynomial ℤ)) (c d : R) : R[X] :=
  ∑ b ∈ Finset.range (Φ.natDegree + 1),
    C (homEval c d ((Φ.coeff b).map (Int.castRingHom R)) (xDegBound Φ * (Φ.natDegree - b))) *
      X ^ b

theorem coeff_scaledPhi (Φ : Polynomial (Polynomial ℤ)) (c d : R) (b : ℕ) :
    (scaledPhi Φ c d).coeff b = if b ≤ Φ.natDegree then
      homEval c d ((Φ.coeff b).map (Int.castRingHom R)) (xDegBound Φ * (Φ.natDegree - b))
      else 0 := by
  simp only [scaledPhi, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

theorem map_scaledPhi {S : Type*} [CommRing S] (f : R →+* S) (Φ : Polynomial (Polynomial ℤ))
    (c d : R) : (scaledPhi Φ c d).map f = scaledPhi Φ (f c) (f d) := by
  have hf : f.comp (Int.castRingHom R) = Int.castRingHom S := RingHom.ext_int _ _
  simp only [scaledPhi, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_homEval f, Polynomial.map_map, hf]

theorem monic_scaledPhi (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic) (c d : R) :
    (scaledPhi Φ c d).Monic := by
  nontriviality R
  refine monic_of_natDegree_le_of_coeff_eq_one Φ.natDegree ?_ ?_
  · refine natDegree_sum_le_of_forall_le _ _ fun b hb => ?_
    have hb' : b ≤ Φ.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    exact (natDegree_C_mul_X_pow_le _ _).trans hb'
  · rw [coeff_scaledPhi, if_pos le_rfl, Nat.sub_self, mul_zero]
    have h1 : Φ.coeff Φ.natDegree = 1 := hΦ.coeff_natDegree
    rw [h1, Polynomial.map_one, homEval_one_zero]

abbrev fibrePoly {F : Type*} [CommRing F] (Φ : Polynomial (Polynomial ℤ)) (x : F) : F[X] :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) x)

theorem monic_fibrePoly {F : Type*} [CommRing F] (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic)
    (x : F) : (fibrePoly Φ x).Monic := hΦ.map _

theorem natDegree_fibrePoly {F : Type*} [CommRing F] [Nontrivial F] (Φ : Polynomial (Polynomial ℤ))
    (hΦ : Φ.Monic) (x : F) : (fibrePoly Φ x).natDegree = Φ.natDegree :=
  hΦ.natDegree_map _

theorem scaledPhi_eq_scaleRoots {F : Type*} [Field F] (Φ : Polynomial (Polynomial ℤ))
    (hΦ : Φ.Monic) (c d : F) (hd : d ≠ 0) :
    scaledPhi Φ c d = (fibrePoly Φ (c / d)).scaleRoots (d ^ xDegBound Φ) := by
  ext b
  rw [coeff_scaledPhi, coeff_scaleRoots, natDegree_fibrePoly Φ hΦ]
  split_ifs with hb
  · rw [homEval_eq_pow_mul_eval c d hd, ← pow_mul, coeff_map, coe_eval₂RingHom, eval_map]
    · ring
    ·
      rcases hb.lt_or_eq with hlt | rfl
      · calc ((Φ.coeff b).map (Int.castRingHom F)).natDegree ≤ (Φ.coeff b).natDegree :=
              natDegree_map_le
          _ ≤ xDegBound Φ := natDegree_coeff_le_xDegBound Φ b
          _ ≤ xDegBound Φ * (Φ.natDegree - b) :=
              Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt hlt)
      · rw [hΦ.coeff_natDegree, Polynomial.map_one, natDegree_one]
        exact Nat.zero_le _
  · rw [coeff_eq_zero_of_natDegree_lt, zero_mul]
    rw [natDegree_fibrePoly Φ hΦ]
    exact not_le.mp hb

theorem eval_scaledPhi {F : Type*} [Field F] (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic)
    (c d : F) (hd : d ≠ 0) (y : F) :
    (scaledPhi Φ c d).eval (d ^ xDegBound Φ * y) =
      (d ^ xDegBound Φ) ^ Φ.natDegree * (fibrePoly Φ (c / d)).eval y := by
  rw [scaledPhi_eq_scaleRoots Φ hΦ c d hd, scaleRoots_eval_mul, natDegree_fibrePoly Φ hΦ]

theorem irreducible_scaleRoots_of_monic {F : Type*} [Field F] {q : F[X]} (hq : q.Monic)
    (hirr : Irreducible q) {s : F} (hs : s ≠ 0) : Irreducible (q.scaleRoots s) := by
  have hmon : (q.scaleRoots s).Monic := (monic_scaleRoots_iff s).2 hq
  rw [hmon.irreducible_iff_natDegree]
  refine ⟨?_, ?_⟩
  · intro h1
    have := congrArg natDegree h1
    rw [natDegree_scaleRoots, natDegree_one] at this
    exact hirr.not_isUnit (hq.natDegree_eq_zero.mp this |> fun h => h ▸ isUnit_one)
  · intro f g hf hg hfg
    have key : f.scaleRoots s⁻¹ * g.scaleRoots s⁻¹ = q := by
      rw [← mul_scaleRoots_of_noZeroDivisors, hfg, ← scaleRoots_mul, mul_inv_cancel₀ hs,
        scaleRoots_one]
    have := (hq.irreducible_iff_natDegree.mp hirr).2 _ _ ((monic_scaleRoots_iff _).2 hf)
      ((monic_scaleRoots_iff _).2 hg) key
    simpa only [natDegree_scaleRoots] using this

end Scaled

section Generic

p2m_open "WeierstrassCurve~evalEval_ψ_sq~evalEval_φ"

universe u

variable (K : Type u) [Field K]

abbrev R5 : Type u := MvPolynomial (Fin 5) K

local notation "LL" => WeierstrassCurve.Generic.FunctionField K
local notation "ΩΩ" => WeierstrassCurve.Generic.Closure K

abbrev EL : WeierstrassCurve LL :=
  (Generic.poly K).map (algebraMap (R5 K) LL)

theorem curve_eq_baseChange : Generic.curve K = (EL K).baseChange ΩΩ := by
  rw [Generic.curve_def, EL, WeierstrassCurve.baseChange, WeierstrassCurve.map_map,
    ← IsScalarTower.algebraMap_eq]

theorem Δ_EL : (EL K).Δ = algebraMap (R5 K) LL (Generic.poly K).Δ :=
  (Generic.poly K).map_Δ _

theorem Δ_EL_ne_zero : (EL K).Δ ≠ 0 := by
  rw [Δ_EL]
  exact (map_ne_zero_iff _ (Generic.algebraMap_functionField_injective K)).2
    (Generic.Δ_poly_ne_zero K)

scoped instance isElliptic_EL : (EL K).IsElliptic := ⟨(Δ_EL_ne_zero K).isUnit⟩

theorem j_eq_div {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] :
    W.j = W.c₄ ^ 3 / W.Δ := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ', div_eq_mul_inv]
  ring

theorem j_EL : (EL K).j = algebraMap (R5 K) LL ((Generic.poly K).c₄ ^ 3) /
    algebraMap (R5 K) LL (Generic.poly K).Δ := by
  rw [j_eq_div, map_c₄, map_Δ, map_pow]

theorem algebraMap_Δ_ne_zero : algebraMap (R5 K) LL (Generic.poly K).Δ ≠ 0 := by
  rw [← Δ_EL]; exact Δ_EL_ne_zero K

def θ : R5 K →+* RatFunc K := by
  classical
  exact (Generic.classify K (WeierstrassCurve.ofJ (RatFunc.X : RatFunc K))).toRingHom

theorem θ_comp_algebraMap : (θ K).comp (algebraMap K (R5 K)) = algebraMap K (RatFunc K) := by
  classical
  exact AlgHom.comp_algebraMap
    (Generic.classify K (WeierstrassCurve.ofJ (RatFunc.X : RatFunc K)))

theorem exists_poly_map_θ : ∃ (W : WeierstrassCurve (RatFunc K)) (_ : W.IsElliptic),
    W.j = RatFunc.X ∧ (Generic.poly K).map (θ K) = W := by
  classical
  exact ⟨WeierstrassCurve.ofJ RatFunc.X, inferInstance, WeierstrassCurve.ofJ_j _,
    Generic.poly_map_classify _⟩

theorem θ_Δ_ne_zero : θ K (Generic.poly K).Δ ≠ 0 := by
  obtain ⟨W, hW, -, hθ⟩ := exists_poly_map_θ K
  rw [← map_Δ, hθ, ← coe_Δ']
  exact W.Δ'.ne_zero

theorem θ_j : θ K ((Generic.poly K).c₄ ^ 3) / θ K (Generic.poly K).Δ = RatFunc.X := by
  obtain ⟨W, hW, hj, hθ⟩ := exists_poly_map_θ K
  rw [map_pow, ← map_Δ, ← map_c₄, hθ, ← j_eq_div, hj]

theorem transcendental_j : Transcendental K (EL K).j := by
  rintro ⟨f, hf0, hf⟩

  let F₀ : R5 K :=
    homEval ((Generic.poly K).c₄ ^ 3) (Generic.poly K).Δ (f.map (algebraMap K (R5 K))) f.natDegree

  have hL : algebraMap (R5 K) LL F₀ = 0 := by
    show algebraMap (R5 K) LL (homEval _ _ _ _) = 0
    rw [map_homEval, Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
      homEval_eq_pow_mul_eval _ _ (algebraMap_Δ_ne_zero K) _ natDegree_map_le,
      ← j_EL, Polynomial.eval_map, ← Polynomial.aeval_def, hf, mul_zero]
  have hF : F₀ = 0 := (map_eq_zero_iff _ (Generic.algebraMap_functionField_injective K)).1 hL

  have hθ : θ K F₀ = (θ K (Generic.poly K).Δ) ^ f.natDegree * aeval (RatFunc.X : RatFunc K) f := by
    show θ K (homEval _ _ _ _) = _
    rw [map_homEval, Polynomial.map_map, θ_comp_algebraMap,
      homEval_eq_pow_mul_eval _ _ (θ_Δ_ne_zero K) _ natDegree_map_le, θ_j,
      Polynomial.eval_map, ← Polynomial.aeval_def]
  rw [hF, map_zero] at hθ
  have ht : aeval (RatFunc.X : RatFunc K) f = 0 :=
    (mul_eq_zero.mp hθ.symm).resolve_left (pow_ne_zero _ (θ_Δ_ne_zero K))
  exact RatFunc.transcendental_X ⟨f, hf0, ht⟩

abbrev gPoly (Φ : Polynomial (Polynomial ℤ)) : (R5 K)[X] :=
  scaledPhi Φ ((Generic.poly K).c₄ ^ 3) (Generic.poly K).Δ

theorem irreducible_gPoly_map {N : ℕ} [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (hN : (N : K) ≠ 0) :
    Irreducible ((gPoly K data.Φ).map (algebraMap (R5 K) LL)) := by
  have hmon : (gPoly K data.Φ).Monic := monic_scaledPhi _ data.monic _ _
  rw [← hmon.irreducible_iff_irreducible_map_fraction_map]

  refine hmon.irreducible_of_irreducible_map (θ K) _ ?_
  rw [map_scaledPhi, scaledPhi_eq_scaleRoots _ data.monic _ _ (θ_Δ_ne_zero K), θ_j]
  refine irreducible_scaleRoots_of_monic (monic_fibrePoly _ data.monic _) ?_
    (pow_ne_zero _ (θ_Δ_ne_zero K))
  have hirr := data.irreducible_map_ratFunc_of_natCast_ne_zero K N hN
  rw [Polynomial.map_map] at hirr
  convert hirr using 2 <;> try rfl
  refine Polynomial.ringHom_ext (fun a => by simp) ?_
  simp [RatFunc.algebraMap_X]

theorem exists_algEquiv_apply_eq_of_isRoot {N : ℕ} [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (hN : (N : K) ≠ 0) {y y' : ΩΩ}
    (hy : (fibrePoly data.Φ (algebraMap LL ΩΩ (EL K).j)).IsRoot y)
    (hy' : (fibrePoly data.Φ (algebraMap LL ΩΩ (EL K).j)).IsRoot y') :
    ∃ σ : ΩΩ ≃ₐ[LL] ΩΩ, σ y = y' := by
  have hdΩL : algebraMap (R5 K) ΩΩ (Generic.poly K).Δ =
      algebraMap LL ΩΩ (algebraMap (R5 K) LL (Generic.poly K).Δ) :=
    IsScalarTower.algebraMap_apply _ _ _ _
  have hd0 : algebraMap (R5 K) ΩΩ (Generic.poly K).Δ ≠ 0 :=
    (map_ne_zero_iff _ (Generic.algebraMap_closure_injective K)).2 (Generic.Δ_poly_ne_zero K)
  have hjΩ : algebraMap LL ΩΩ (EL K).j =
      algebraMap (R5 K) ΩΩ ((Generic.poly K).c₄ ^ 3) / algebraMap (R5 K) ΩΩ (Generic.poly K).Δ := by
    rw [j_EL, map_div₀, hdΩL, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hgLmon : ((gPoly K data.Φ).map (algebraMap (R5 K) LL)).Monic :=
    (monic_scaledPhi _ data.monic _ _).map _
  have hgLirr := irreducible_gPoly_map K data hN

  have hroot : ∀ z : ΩΩ, (fibrePoly data.Φ (algebraMap LL ΩΩ (EL K).j)).IsRoot z →
      aeval (algebraMap (R5 K) ΩΩ (Generic.poly K).Δ ^ xDegBound data.Φ * z)
        ((gPoly K data.Φ).map (algebraMap (R5 K) LL)) = 0 := by
    intro z hz
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_map,
      ← IsScalarTower.algebraMap_eq, map_scaledPhi, eval_scaledPhi _ data.monic _ _ hd0, ← hjΩ,
      hz.eq_zero, mul_zero]
  have hmin : ∀ z : ΩΩ, (fibrePoly data.Φ (algebraMap LL ΩΩ (EL K).j)).IsRoot z →
      minpoly LL (algebraMap (R5 K) ΩΩ (Generic.poly K).Δ ^ xDegBound data.Φ * z) =
        (gPoly K data.Φ).map (algebraMap (R5 K) LL) := fun z hz =>
    (minpoly.eq_of_irreducible_of_monic hgLirr (hroot z hz) hgLmon).symm
  have hconj := (hmin y' hy').trans (hmin y hy).symm
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := LL) (E := ΩΩ)).mp hconj
  refine ⟨σ, ?_⟩
  have hσ' : σ (algebraMap (R5 K) ΩΩ (Generic.poly K).Δ ^ xDegBound data.Φ * y) =
      algebraMap (R5 K) ΩΩ (Generic.poly K).Δ ^ xDegBound data.Φ * y' := hσ
  rw [map_mul, map_pow, hdΩL, AlgEquiv.commutes, ← hdΩL] at hσ'
  exact mul_left_cancel₀ (pow_ne_zero _ hd0) hσ'

end Generic

section Points

p2m_open "WeierstrassCurve~evalEval_ψ_sq~evalEval_φ WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"
open scoped Polynomial.Bivariate

variable {F : Type*} [Field F]

theorem evalEval_eq_of_mk_eq {W : WeierstrassCurve F} {f g : F[X][Y]}
    (hfg : Affine.CoordinateRing.mk W f = Affine.CoordinateRing.mk W g) {x y : F}
    (hxy : W.toAffine.Equation x y) : f.evalEval x y = g.evalEval x y := by
  obtain ⟨r, hr⟩ := AdjoinRoot.mk_eq_mk.mp hfg
  have h : (f - g).evalEval x y = 0 := by
    rw [hr, evalEval_mul, show W.toAffine.polynomial.evalEval x y = 0 from hxy, zero_mul]
  rwa [evalEval_sub, sub_eq_zero] at h

theorem evalEval_φ {W : WeierstrassCurve F} (n : ℤ) {x y : F} (hxy : W.toAffine.Equation x y) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  rw [evalEval_eq_of_mk_eq (Affine.CoordinateRing.mk_φ W n) hxy, evalEval_C]

theorem evalEval_ψ_sq {W : WeierstrassCurve F} (n : ℤ) {x y : F} (hxy : W.toAffine.Equation x y) :
    (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  have h : Affine.CoordinateRing.mk W (W.ψ n ^ 2) = Affine.CoordinateRing.mk W (C (W.ΨSq n)) := by
    rw [map_pow, Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]
  rw [← evalEval_pow, evalEval_eq_of_mk_eq h hxy, evalEval_C]

theorem exists_nonsingular [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic] (x : F) :
    ∃ y : F, W.toAffine.Nonsingular x y := by
  let q : F[X] := C 1 * X ^ 2 + C (W.a₁ * x + W.a₃) * X +
    C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
  have hq : q.degree = 2 := degree_quadratic one_ne_zero
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hq]; exact two_ne_zero)
  refine ⟨y, (Affine.equation_iff_nonsingular ..).mp ?_⟩
  rw [Affine.equation_iff]
  have h : q.eval y = 0 := hy
  simp only [q, eval_add, eval_mul, eval_C, eval_pow, eval_X, one_mul] at h
  linear_combination h

variable [DecidableEq F]

theorem inLine_of_zsmul_eq (W : WeierstrassCurve F) [W.IsElliptic] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {x₀ y₀ x y : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)
    (h : W.toAffine.Nonsingular x y) (hP₀ : p • Point.some x₀ y₀ h₀ = 0) (a : ℤ)
    (ha : a • Point.some x₀ y₀ h₀ = Point.some x y h) : ModularCurve.InLine W p x₀ x := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos

  set b : ℕ := (a % p).toNat with hb
  have hbz : (b : ℤ) = a % p := Int.toNat_of_nonneg (Int.emod_nonneg _ hp0.ne')
  have hbp : b < p := by
    have := Int.emod_lt_of_pos a hp0
    omega
  have hbP : (b : ℤ) • Point.some x₀ y₀ h₀ = Point.some x y h := by
    rw [hbz, ← ha]
    conv_rhs => rw [← Int.emod_add_mul_ediv a p]
    rw [add_zsmul, mul_comm, mul_smul, natCast_zsmul, hP₀, smul_zero, add_zero]
  have hb0 : b ≠ 0 := by
    intro hb0
    rw [hb0, Nat.cast_zero, zero_zsmul] at hbP
    exact Point.some_ne_zero _ hbP.symm

  have key : ∀ (n : ℤ) {x' y' : F} (h' : W.toAffine.Nonsingular x' y'),
      n • Point.some x₀ y₀ h₀ = Point.some x' y' h' →
        x' * (W.ΨSq n).eval x₀ = (W.Φ n).eval x₀ := by
    intro n x' y' h' hn
    have e := Point.zsmul_x_mul_psi_sq W n h₀ h' hn
    rwa [evalEval_ψ_sq n h₀.left, evalEval_φ n h₀.left] at e
  by_cases hle : b ≤ (p - 1) / 2
  · exact ⟨b, Nat.one_le_iff_ne_zero.mpr hb0, hle, key b h hbP⟩
  ·
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
    refine ⟨p - b, by omega, by omega, key (p - b : ℕ) ((nonsingular_neg ..).mpr h) ?_⟩
    rw [Nat.cast_sub hbp.le, sub_zsmul, natCast_zsmul, hP₀, zero_add, hbP, neg_some]

end Points

section Main

p2m_open "WeierstrassCurve~evalEval_ψ_sq~evalEval_φ WeierstrassCurve.Affine"

universe u

variable (K : Type u) [Field K]

local notation "LL" => WeierstrassCurve.Generic.FunctionField K
local notation "ΩΩ" => WeierstrassCurve.Generic.Closure K

theorem natCard_torsion_EL [DecidableEq (WeierstrassCurve.Generic.Closure K)] (N : ℕ) [NeZero N]
    (hN : (N : WeierstrassCurve.Generic.Closure K) ≠ 0) :
    Nat.card {Q : ((EL K).baseChange ΩΩ).toAffine.Point // N • Q = 0} = N ^ 2 := by
  obtain ⟨e⟩ := (EL K).nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := ΩΩ) hN
  have h1 : Nat.card (Submodule.torsionBy ℤ ((EL K).baseChange ΩΩ).toAffine.Point N) = N ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  rw [← h1]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun Q => ?_)
  rw [Submodule.mem_torsionBy_iff]
  change N • Q = 0 ↔ ((N : ℤ)) • Q = 0
  rw [natCast_zsmul]

theorem main {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    {x x' : WeierstrassCurve.Generic.Closure K}
    (hx : ((WeierstrassCurve.Generic.curve K).preΨ p).eval x = 0)
    (hx' : ((WeierstrassCurve.Generic.curve K).preΨ p).eval x' = 0) :
    ∃ σ : ΩΩ ≃ₐ[LL] ΩΩ, ModularCurve.InLine (WeierstrassCurve.Generic.curve K) p (σ x) x' := by
  classical
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p
  rw [curve_eq_baseChange] at hx hx' ⊢
  set E : WeierstrassCurve ΩΩ := (EL K).baseChange ΩΩ with hE
  haveI : E.IsElliptic := show ((EL K).map (algebraMap LL ΩΩ)).IsElliptic from inferInstance
  have hodd : Odd p := hp.out.odd_of_ne_two hp2

  have hpL : (p : LL) ≠ 0 := fun h => hpK <| (algebraMap K LL).injective (by simpa using h)
  have hpΩ : (p : ΩΩ) ≠ 0 := fun h => hpL <| (algebraMap LL ΩΩ).injective (by simpa using h)

  obtain ⟨y, hxy⟩ := exists_nonsingular E x
  obtain ⟨y', hxy'⟩ := exists_nonsingular E x'
  set P : E.toAffine.Point := Point.some x y hxy with hPdef
  set P' : E.toAffine.Point := Point.some x' y' hxy' with hP'def
  have hPp : p • P = 0 :=
    (Point.nsmul_some_eq_zero_iff_eval_prePsi E hodd hxy).2 (by rwa [← preΨ_ofNat])
  have hP'p : p • P' = 0 :=
    (Point.nsmul_some_eq_zero_iff_eval_prePsi E hodd hxy').2 (by rwa [← preΨ_ofNat])
  have hP0 : P ≠ 0 := by rw [hPdef]; exact Point.some_ne_zero _
  have hP'0 : P' ≠ 0 := by rw [hP'def]; exact Point.some_ne_zero _

  obtain ⟨Θ, hΘ⟩ :=
    WeierstrassCurve.exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j
      K p data LL ΩΩ hpL (EL K) (transcendental_j K) (natCard_torsion_EL K p hpΩ)

  have hcard : ∀ Q : E.toAffine.Point, p • Q = 0 → Q ≠ 0 →
      IsAddCyclic (AddSubgroup.zmultiples Q) ∧ Nat.card (AddSubgroup.zmultiples Q) = p :=
    fun Q hQ hQ0 => ⟨inferInstance, by rw [Nat.card_zmultiples, addOrderOf_eq_prime hQ hQ0]⟩
  let H : {H : AddSubgroup E.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p} :=
    ⟨AddSubgroup.zmultiples P, hcard P hPp hP0⟩
  let H' : {H : AddSubgroup E.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p} :=
    ⟨AddSubgroup.zmultiples P', hcard P' hP'p hP'0⟩

  obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_isRoot K data hpK (Θ H).2 (Θ H').2

  set σP : E.toAffine.Point := Point.map (σ : ΩΩ →ₐ[LL] ΩΩ) P with hσPdef
  have hσPp : p • σP = 0 := by rw [hσPdef, ← map_nsmul, hPp, map_zero]
  have hσP0 : σP ≠ 0 := by
    rw [hσPdef, hPdef, Point.map_some]; exact Point.some_ne_zero _
  let H₂ : {H : AddSubgroup E.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p} :=
    ⟨AddSubgroup.zmultiples σP, hcard σP hσPp hσP0⟩
  have hH₂ : H₂.1 = H.1.map (Point.map (σ : ΩΩ →ₐ[LL] ΩΩ)) := by
    show AddSubgroup.zmultiples σP = (AddSubgroup.zmultiples P).map _
    rw [AddMonoidHom.map_zmultiples]
  have hΘ₂ : ((Θ H₂).1 : ΩΩ) = (Θ H').1 := (hΘ σ H H₂ hH₂).trans hσ
  have hHH : H₂ = H' := Θ.injective (Subtype.ext hΘ₂)

  have hmem : P' ∈ AddSubgroup.zmultiples σP := by
    have : AddSubgroup.zmultiples σP = AddSubgroup.zmultiples P' := congrArg Subtype.val hHH
    rw [this]; exact AddSubgroup.mem_zmultiples P'
  obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  exact ⟨σ, inLine_of_zsmul_eq E hp2 _ hxy' hσPp a ha⟩

end Main

end P2MKcGenX0Irr
p2m_reactivate "P2MW.S_WeierstrassCurve_Generic_exists_algEquiv_inLine_of_eval_prePsi_eq_zero_of_ne_zero.P2MKcGenX0Irr"

open P2MKcGenX0Irr in
universe u in
theorem solution
    {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0)
    {x x' : WeierstrassCurve.Generic.Closure K}
    (hx : ((WeierstrassCurve.Generic.curve K).preΨ p).eval x = 0)
    (hx' : ((WeierstrassCurve.Generic.curve K).preΨ p).eval x' = 0) :
    ∃ σ : WeierstrassCurve.Generic.Closure K ≃ₐ[WeierstrassCurve.Generic.FunctionField K]
        WeierstrassCurve.Generic.Closure K,
      ModularCurve.InLine (WeierstrassCurve.Generic.curve K) p (σ x) x' :=
  P2MKcGenX0Irr.main K hp2 hp hx hx'

end
end S_WeierstrassCurve_Generic_exists_algEquiv_inLine_of_eval_prePsi_eq_zero_of_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_Generic_exists_algEquiv_inLine_of_eval_prePsi_eq_zero_of_ne_zero (solution)
