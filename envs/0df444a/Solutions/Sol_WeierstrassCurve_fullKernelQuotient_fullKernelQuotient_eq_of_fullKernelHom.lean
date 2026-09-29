-- Prove2me | solution 1 for WeierstrassCurve.fullKernelQuotient_fullKernelQuotient_eq_of_fullKernelHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/776d2943-c97a-5ada-8de8-730e625b3b76

import Mathlib
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Theorems.Thm_WeierstrassCurve_exists_fullKernelHom
import Theorems.Thm_WeierstrassCurve_fullKernelHom_surjective_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_eq_of_infinite_setOf_equation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_fullKernelQuotient_fullKernelQuotient_eq_of_fullKernelHom
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"

set_option autoImplicit false

open WeierstrassCurve

namespace P2MTower

section Reindex

variable {M : Type*} [AddCommGroup M]

theorem sum_range_mul_eq (g : ℕ → M) (d m : ℕ) :
    ∑ i ∈ Finset.range (d * m), g i =
      ∑ k ∈ Finset.range d, ∑ j ∈ Finset.range m, g (j + m * k) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring

theorem sum_Icc_eq_sum_range_sub (h : ℕ → M) {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 (n - 1), h i = ∑ i ∈ Finset.range n, h i - h 0 := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ', Nat.add_sub_cancel, add_sub_cancel_right]
  refine Finset.sum_nbij' (fun i => i - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [Finset.mem_Icc] at hi; simp only [Finset.mem_range]; omega
  · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
  · intro i hi; simp only [Finset.mem_Icc] at hi; beta_reduce; omega
  · intro k hk; beta_reduce; omega
  · intro i hi; simp only [Finset.mem_Icc] at hi; beta_reduce; congr 1; omega

variable {A : Type*} [AddCommMonoid A]

theorem velu_reindex (f : A → M) (P Q : A) {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (f P + ∑ k ∈ Finset.Icc 1 (d - 1), (f (P + k • (m • Q)) - f (k • (m • Q)))) +
      ∑ j ∈ Finset.Icc 1 (m - 1),
        ((f (P + j • Q) + ∑ k ∈ Finset.Icc 1 (d - 1),
            (f (P + j • Q + k • (m • Q)) - f (k • (m • Q)))) -
          (f (j • Q) + ∑ k ∈ Finset.Icc 1 (d - 1),
            (f (j • Q + k • (m • Q)) - f (k • (m • Q))))) =
      f P + ∑ i ∈ Finset.Icc 1 (d * m - 1), (f (P + i • Q) - f (i • Q)) := by
  set g : ℕ → M := fun i => f (P + i • Q) - f (i • Q) with hg
  have hkm : ∀ j k : ℕ, j • Q + k • (m • Q) = (j + m * k) • Q := fun j k => by
    rw [add_nsmul, mul_nsmul]

  have hbr : ∀ R : A, f R + ∑ k ∈ Finset.Icc 1 (d - 1), (f (R + k • (m • Q)) - f (k • (m • Q))) =
      f 0 + ∑ k ∈ Finset.range d, (f (R + k • (m • Q)) - f (k • (m • Q))) := by
    intro R
    rw [sum_Icc_eq_sum_range_sub (fun k => f (R + k • (m • Q)) - f (k • (m • Q))) hd]
    simp only [zero_smul, add_zero]
    abel

  have hdiff : ∀ j : ℕ,
      (f 0 + ∑ k ∈ Finset.range d, (f (P + j • Q + k • (m • Q)) - f (k • (m • Q)))) -
        (f 0 + ∑ k ∈ Finset.range d, (f (j • Q + k • (m • Q)) - f (k • (m • Q)))) =
      ∑ k ∈ Finset.range d, g (j + m * k) := by
    intro j
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hg]
    simp only
    rw [add_assoc, hkm]
    abel
  have hfirst : f 0 + ∑ k ∈ Finset.range d, (f (P + k • (m • Q)) - f (k • (m • Q))) =
      f 0 + ∑ k ∈ Finset.range d, g (0 + m * k) := by
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hg]
    simp only
    rw [← hkm 0 k, zero_smul, zero_add]

  have hL : (f P + ∑ k ∈ Finset.Icc 1 (d - 1), (f (P + k • (m • Q)) - f (k • (m • Q)))) +
      ∑ j ∈ Finset.Icc 1 (m - 1),
        ((f (P + j • Q) + ∑ k ∈ Finset.Icc 1 (d - 1),
            (f (P + j • Q + k • (m • Q)) - f (k • (m • Q)))) -
          (f (j • Q) + ∑ k ∈ Finset.Icc 1 (d - 1),
            (f (j • Q + k • (m • Q)) - f (k • (m • Q))))) =
      f 0 + ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range d, g (j + m * k) := by
    rw [hbr P, hfirst]
    have hj : ∀ j ∈ Finset.Icc 1 (m - 1),
        ((f (P + j • Q) + ∑ k ∈ Finset.Icc 1 (d - 1),
            (f (P + j • Q + k • (m • Q)) - f (k • (m • Q)))) -
          (f (j • Q) + ∑ k ∈ Finset.Icc 1 (d - 1),
            (f (j • Q + k • (m • Q)) - f (k • (m • Q))))) =
        ∑ k ∈ Finset.range d, g (j + m * k) := by
      intro j _
      rw [hbr (P + j • Q), hbr (j • Q), hdiff j]
    rw [Finset.sum_congr rfl hj,
      sum_Icc_eq_sum_range_sub (fun j => ∑ k ∈ Finset.range d, g (j + m * k)) hm]
    abel

  have hR : f P + ∑ i ∈ Finset.Icc 1 (d * m - 1), (f (P + i • Q) - f (i • Q)) =
      f 0 + ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range d, g (j + m * k) := by
    have h1 : 1 ≤ d * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    rw [show (∑ i ∈ Finset.Icc 1 (d * m - 1), (f (P + i • Q) - f (i • Q))) =
        ∑ i ∈ Finset.Icc 1 (d * m - 1), g i from rfl,
      sum_Icc_eq_sum_range_sub g h1, sum_range_mul_eq g d m, Finset.sum_comm, hg]
    simp only [zero_smul, add_zero]
    abel
  rw [hL, hR]

end Reindex

section Orders

variable {A : Type*} [AddCommGroup A]

theorem zmultiples_nsmul_le (Q : A) (m : ℕ) :
    AddSubgroup.zmultiples (m • Q) ≤ AddSubgroup.zmultiples Q :=
  AddSubgroup.zmultiples_le_of_mem ((AddSubgroup.zmultiples Q).nsmul_mem
    (AddSubgroup.mem_zmultiples Q) m)

theorem not_mem_zmultiples_nsmul {Q P : A} (m : ℕ) (hP : P ∉ AddSubgroup.zmultiples Q) :
    P ∉ AddSubgroup.zmultiples (m • Q) := fun h => hP (zmultiples_nsmul_le Q m h)

theorem add_nsmul_not_mem_zmultiples_nsmul {Q P : A} (m j : ℕ)
    (hP : P ∉ AddSubgroup.zmultiples Q) : P + j • Q ∉ AddSubgroup.zmultiples (m • Q) := by
  intro h
  apply hP
  have h' := zmultiples_nsmul_le Q m h
  have := (AddSubgroup.zmultiples Q).sub_mem h'
    ((AddSubgroup.zmultiples Q).nsmul_mem (AddSubgroup.mem_zmultiples Q) j)
  rwa [add_sub_cancel_right] at this

theorem nsmul_not_mem_zmultiples_nsmul {Q : A} {d m j : ℕ} (hQ : addOrderOf Q = d * m)
    (hj1 : 1 ≤ j) (hjm : j ≤ m - 1) : j • Q ∉ AddSubgroup.zmultiples (m • Q) := by
  intro h
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp h

  have h0 : ((j : ℤ) - z * m) • Q = 0 := by
    rw [sub_zsmul, mul_zsmul, natCast_zsmul, natCast_zsmul, hz]
    abel
  have hdvd : ((addOrderOf Q : ℕ) : ℤ) ∣ (j : ℤ) - z * m :=
    (addOrderOf_dvd_iff_zsmul_eq_zero).mpr h0
  rw [hQ, Nat.cast_mul] at hdvd
  have hm : (m : ℤ) ∣ (j : ℤ) := by
    have h1 : (m : ℤ) ∣ (j : ℤ) - z * m := dvd_trans (Dvd.intro_left _ rfl) hdvd
    have h2 : (m : ℤ) ∣ z * m := Dvd.intro_left _ rfl
    simpa using dvd_add h1 h2
  have : m ∣ j := by exact_mod_cast hm
  have := Nat.le_of_dvd (by omega) this
  omega

theorem addOrderOf_nsmul_eq {Q : A} {d m : ℕ} (hQ : addOrderOf Q = d * m) (hm : m ≠ 0) :
    addOrderOf (m • Q) = d := by
  rw [addOrderOf_nsmul_of_dvd hm (hQ ▸ Dvd.intro_left d rfl), hQ,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm)]

end Orders

section Points

variable {K : Type*} [Field K]

theorem equation_of_ne_zero {V : WeierstrassCurve K} {X : V.toAffine.Point} (hX : X ≠ 0) :
    V.toAffine.Equation X.coordsOrZero.1 X.coordsOrZero.2 := by
  rcases X with _ | ⟨x, y, h⟩
  · exact absurd rfl hX
  · exact h.1

theorem setOf_equation_infinite [IsAlgClosed K] (V : WeierstrassCurve K) :
    {xy : K × K | V.toAffine.Equation xy.1 xy.2}.Infinite := by
  have hy : ∀ x : K, ∃ y : K, V.toAffine.Equation x y := by
    intro x
    set b : K := V.a₁ * x + V.a₃ with hb
    set c : K := -(x ^ 3 + V.a₂ * x ^ 2 + V.a₄ * x + V.a₆) with hc
    have hp : (Polynomial.C (1 : K) * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
        Polynomial.C c).degree = 2 := Polynomial.degree_quadratic one_ne_zero
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ (by rw [hp]; decide)
    refine ⟨y, ?_⟩
    rw [WeierstrassCurve.Affine.equation_iff]
    have h0 : 1 * y ^ 2 + b * y + c = 0 := by
      have := hy.eq_zero
      simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_pow] using this
    rw [hb, hc] at h0
    linear_combination h0
  choose yOf hyOf using hy
  have hinj : Function.Injective fun x : K => (x, yOf x) := fun x x' h => (Prod.mk.inj h).1
  exact Set.infinite_of_injective_forall_mem hinj fun x => hyOf x

end Points

end P2MTower

open P2MTower in

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] {d m : ℕ} [NeZero d] [NeZero m]
    (hN : ((d * m : ℕ) : K) ≠ 0) (Q : W.toAffine.Point) (hQ : addOrderOf Q = d * m)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient (m • Q) d).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples (m • Q))
    (hφ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples (m • Q) →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (d - 1),
            ((P + k • (m • Q)).coordsOrZero.1 - (k • (m • Q)).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (d - 1),
            ((P + k • (m • Q)).coordsOrZero.2 - (k • (m • Q)).coordsOrZero.2))) :
    (W.fullKernelQuotient (m • Q) d).fullKernelQuotient (φ Q) m = W.fullKernelQuotient Q (d * m) := by
  have hd0 : d ≠ 0 := NeZero.ne d
  have hm0 : m ≠ 0 := NeZero.ne m
  haveI : NeZero (d * m) := ⟨Nat.mul_ne_zero hd0 hm0⟩
  have hdK : (d : K) ≠ 0 := fun h => hN (by rw [Nat.cast_mul, h, zero_mul])
  have hmK : (m : K) ≠ 0 := fun h => hN (by rw [Nat.cast_mul, h, mul_zero])
  have hTord : addOrderOf (m • Q) = d := addOrderOf_nsmul_eq hQ hm0

  have hΔ₁ : (W.fullKernelQuotient (m • Q) d).Δ ≠ 0 := WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero d W hdK (m • Q) hTord
  haveI : (W.fullKernelQuotient (m • Q) d).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ₁⟩
  have hΔ' : (W.fullKernelQuotient Q (d * m)).Δ ≠ 0 := WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero (d * m) W hN Q hQ
  haveI hWell : (W.fullKernelQuotient Q (d * m)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩

  have hφQ : addOrderOf (φ Q) = m := by
    refine (addOrderOf_eq_iff (Nat.pos_of_ne_zero hm0)).mpr ⟨?_, fun j hjm hj0 => ?_⟩
    · rw [← map_nsmul, ← AddMonoidHom.mem_ker, hφker]
      exact AddSubgroup.mem_zmultiples (m • Q)
    · rw [← map_nsmul, Ne, ← AddMonoidHom.mem_ker, hφker]
      exact nsmul_not_mem_zmultiples_nsmul hQ hj0 (by omega)

  obtain ⟨ψ, hψker, hψ⟩ := WeierstrassCurve.exists_fullKernelHom (W.fullKernelQuotient (m • Q) d) hmK (φ Q) hφQ
  obtain ⟨χ, hχker, hχ⟩ := WeierstrassCurve.exists_fullKernelHom W hN Q hQ
  have hχsurj : Function.Surjective χ :=
    WeierstrassCurve.fullKernelHom_surjective_of_isAlgClosed W hN Q hQ χ hχker hχ

  have hcoord : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (ψ (φ P)).coordsOrZero = (χ P).coordsOrZero := by
    intro P hP
    have hPT : P ∉ AddSubgroup.zmultiples (m • Q) := not_mem_zmultiples_nsmul m hP
    have hφP : φ P ∉ AddSubgroup.zmultiples (φ Q) := by
      intro h
      rw [← AddMonoidHom.map_zmultiples] at h
      obtain ⟨R, hR, hRP⟩ := AddSubgroup.mem_map.mp h
      have hker : P - R ∈ φ.ker := by
        rw [AddMonoidHom.mem_ker, map_sub, hRP, sub_self]
      rw [hφker] at hker
      exact hP (by simpa using (AddSubgroup.zmultiples Q).add_mem (zmultiples_nsmul_le Q m hker) hR)
    rw [hψ (φ P) hφP, hχ P hP]

    have hj : ∀ j ∈ Finset.Icc 1 (m - 1),
        (φ P + j • φ Q).coordsOrZero = ((P + j • Q).coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (d - 1),
            ((P + j • Q + k • (m • Q)).coordsOrZero.1 - (k • (m • Q)).coordsOrZero.1),
          (P + j • Q).coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (d - 1),
            ((P + j • Q + k • (m • Q)).coordsOrZero.2 - (k • (m • Q)).coordsOrZero.2)) ∧
        (j • φ Q).coordsOrZero = ((j • Q).coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (d - 1),
            ((j • Q + k • (m • Q)).coordsOrZero.1 - (k • (m • Q)).coordsOrZero.1),
          (j • Q).coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (d - 1),
            ((j • Q + k • (m • Q)).coordsOrZero.2 - (k • (m • Q)).coordsOrZero.2)) := by
      intro j hjm
      rw [Finset.mem_Icc] at hjm
      rw [← map_nsmul, ← map_add]
      exact ⟨hφ _ (add_nsmul_not_mem_zmultiples_nsmul m j hP),
        hφ _ (nsmul_not_mem_zmultiples_nsmul hQ hjm.1 hjm.2)⟩
    rw [hφ P hPT]
    have hs1 : (∑ j ∈ Finset.Icc 1 (m - 1),
        ((φ P + j • φ Q).coordsOrZero.1 - (j • φ Q).coordsOrZero.1)) =
        ∑ j ∈ Finset.Icc 1 (m - 1),
          (((P + j • Q).coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (d - 1),
              ((P + j • Q + k • (m • Q)).coordsOrZero.1 - (k • (m • Q)).coordsOrZero.1)) -
            ((j • Q).coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (d - 1),
              ((j • Q + k • (m • Q)).coordsOrZero.1 - (k • (m • Q)).coordsOrZero.1))) :=
      Finset.sum_congr rfl fun j hjm => by rw [(hj j hjm).1, (hj j hjm).2]
    have hs2 : (∑ j ∈ Finset.Icc 1 (m - 1),
        ((φ P + j • φ Q).coordsOrZero.2 - (j • φ Q).coordsOrZero.2)) =
        ∑ j ∈ Finset.Icc 1 (m - 1),
          (((P + j • Q).coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (d - 1),
              ((P + j • Q + k • (m • Q)).coordsOrZero.2 - (k • (m • Q)).coordsOrZero.2)) -
            ((j • Q).coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (d - 1),
              ((j • Q + k • (m • Q)).coordsOrZero.2 - (k • (m • Q)).coordsOrZero.2))) :=
      Finset.sum_congr rfl fun j hjm => by rw [(hj j hjm).1, (hj j hjm).2]
    rw [hs1, hs2]
    exact Prod.ext
      (velu_reindex (fun X : W.toAffine.Point => X.coordsOrZero.1) P Q
        (Nat.one_le_iff_ne_zero.mpr hd0) (Nat.one_le_iff_ne_zero.mpr hm0))
      (velu_reindex (fun X : W.toAffine.Point => X.coordsOrZero.2) P Q
        (Nat.one_le_iff_ne_zero.mpr hd0) (Nat.one_le_iff_ne_zero.mpr hm0))

  have hsub : {xy : K × K | (W.fullKernelQuotient Q (d * m)).toAffine.Equation xy.1 xy.2} ⊆
      {xy : K × K | ((W.fullKernelQuotient (m • Q) d).fullKernelQuotient (φ Q) m).toAffine.Equation xy.1 xy.2 ∧
        (W.fullKernelQuotient Q (d * m)).toAffine.Equation xy.1 xy.2} := by
    rintro ⟨x, y⟩ hxy
    refine ⟨?_, hxy⟩
    have hns : (W.fullKernelQuotient Q (d * m)).toAffine.Nonsingular x y := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hxy
    obtain ⟨P, hP⟩ := hχsurj (WeierstrassCurve.Affine.Point.some x y hns)
    have hPQ : P ∉ AddSubgroup.zmultiples Q := by
      intro h
      rw [← hχker, AddMonoidHom.mem_ker, hP] at h
      exact WeierstrassCurve.Affine.Point.some_ne_zero hns h
    have hne : ψ (φ P) ≠ 0 := by
      intro h0
      have hcz := hcoord P hPQ
      rw [h0, hP] at hcz

      have : φ P ∈ ψ.ker := h0
      rw [hψker, ← AddMonoidHom.map_zmultiples] at this
      obtain ⟨R, hR, hRP⟩ := AddSubgroup.mem_map.mp this
      have hker : P - R ∈ φ.ker := by rw [AddMonoidHom.mem_ker, map_sub, hRP, sub_self]
      rw [hφker] at hker
      exact hPQ (by simpa using (AddSubgroup.zmultiples Q).add_mem (zmultiples_nsmul_le Q m hker) hR)
    have heq := equation_of_ne_zero hne
    rw [hcoord P hPQ, hP] at heq
    exact heq
  have hinf := (setOf_equation_infinite (W.fullKernelQuotient Q (d * m))).mono hsub
  exact WeierstrassCurve.eq_of_infinite_setOf_equation hinf

end S_WeierstrassCurve_fullKernelQuotient_fullKernelQuotient_eq_of_fullKernelHom
end P2MW
export P2MW.S_WeierstrassCurve_fullKernelQuotient_fullKernelQuotient_eq_of_fullKernelHom (solution)
