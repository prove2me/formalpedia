-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectSemilocalDifferentialTraceRegularity.functionFieldDifferentialTrace_mem_rationalAdic_of_mem_directFactorLattices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:48:38.309469+00:00
-- url     : https://prove2.me/submissions/7a992c40-a7d4-4d99-a079-658b98fb0475

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialTraceRegularity
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalUniformizer
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalDifferentialTraceRegularity
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_logarithmicDifferential_isGlobalSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_localDifferentialLattice_iff_differentialOrder_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_logarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectIntegralDifferentialTraceRegularity_functionFieldDifferentialTrace_directIntegral_smul_differential_mem_rationalAdic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalDenominator_exists_directSemilocal_integral_multiple
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalUniformizer_exists_directSemilocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply


section
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalDifferentialTraceRegularity
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
open QEC.Coding.AlgebraicGeometry
open FunctionFieldDifferential
open DirectIntegralDifferentialTraceRegularity
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] semilocalDifferentialTraceRegularity_Algebra_1
attribute [local instance] semilocalDifferentialTraceRegularity_ScalarTower_1
open DirectIntegralDifferentialResidue
private theorem differentialOrder_logarithmic_eq_neg_one_of_order_eq_one
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0)
    (horder : P.order f = 1) :
    differentialOrder (k := k) (F := F) P
        (Differential.logarithmicDifferential (k := k) (F := F) f)
        (logarithmicDifferential_ne_zero_of_order_eq_one k F P f hf horder) =
      -1 := by
  let omega := Differential.logarithmicDifferential (k := k) (F := F) f
  let homega : omega ≠ 0 :=
    logarithmicDifferential_ne_zero_of_order_eq_one k F P f hf horder
  have hsimple : omega ∈ Differential.simplePoleDifferentialLattice P :=
    Differential.logarithmicDifferential_isGlobalSimplePole
      (k := k) (F := F) f hf P
  have hresidue :
      Differential.simplePoleResidue (k := k) (F := F) P
          (Differential.logarithmicDifferentialAtSimplePole
            (k := k) (F := F) P f hf) = 1 := by
    simpa only [horder, Int.cast_one] using
      (Differential.simplePoleResidue_logarithmicDifferential
        (k := k) (F := F) P f hf)
  have hnotRegular : omega ∉ Differential.localDifferentialLattice P := by
    intro hregular
    have hzero :=
      Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
        (k := k) (F := F) P
        (Differential.logarithmicDifferentialAtSimplePole
          (k := k) (F := F) P f hf) hregular
    rw [hresidue] at hzero
    exact one_ne_zero hzero
  have hge : -1 ≤ differentialOrder
      (k := k) (F := F) P omega homega :=
    (Differential.mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
      (k := k) (F := F) P omega homega).mp hsimple
  have hnge : ¬ 0 ≤ differentialOrder
      (k := k) (F := F) P omega homega := by
    intro hnonnegative
    apply hnotRegular
    exact
      (Differential.mem_localDifferentialLattice_iff_differentialOrder_nonnegative
        (k := k) (F := F) P omega homega).mpr hnonnegative
  apply le_antisymm
  · exact Int.le_sub_one_iff.mpr (lt_of_not_ge hnge)
  · exact hge
private theorem differential_eq_smul_logarithmicDifferential
    (f : F) (hf : f ≠ 0) :
    differential k F f =
      f • Differential.logarithmicDifferential (k := k) (F := F) f := by
  rw [Differential.logarithmicDifferential, smul_smul,
    mul_inv_cancel₀ hf, one_smul]
private theorem differentialOrder_differential_eq_zero_of_order_eq_one
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0)
    (horder : P.order f = 1) (hdf : differential k F f ≠ 0) :
    differentialOrder (k := k) (F := F) P
        (differential k F f) hdf = 0 := by
  let omega := Differential.logarithmicDifferential (k := k) (F := F) f
  let homega : omega ≠ 0 :=
    logarithmicDifferential_ne_zero_of_order_eq_one k F P f hf horder
  have hlogOrder : differentialOrder
      (k := k) (F := F) P omega homega = -1 :=
    differentialOrder_logarithmic_eq_neg_one_of_order_eq_one
      k F P f hf horder
  have hscaled : differentialOrder (k := k) (F := F) P
      (f • omega) (smul_ne_zero hf homega) = 0 := by
    rw [Differential.differentialOrder_smul
      (k := k) (F := F) P f hf omega homega, horder, hlogOrder]
    norm_num
  simpa only [differential_eq_smul_logarithmicDifferential k F f hf] using
    hscaled
end QEC.Coding.AlgebraicGeometry.DirectSemilocalDifferentialTraceRegularity
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSemilocalDifferentialTraceRegularity
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
open QEC.Coding.AlgebraicGeometry
open FunctionFieldDifferential
open DirectIntegralDifferentialTraceRegularity
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalDifferentialTraceRegularity.semilocalDifferentialTraceRegularity_Algebra_1
attribute [local instance] semilocalDifferentialTraceRegularity_Algebra_1
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalDifferentialTraceRegularity.semilocalDifferentialTraceRegularity_ScalarTower_1
attribute [local instance] semilocalDifferentialTraceRegularity_ScalarTower_1
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalDifferentialTraceRegularity._p2m_local_instance_e20b542250_58
open DirectIntegralDifferentialResidue
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalDifferentialTraceRegularity
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (omega : Differential k F)
    (homega : ∀ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      omega ∈ Differential.localDifferentialLattice
        (AffinePlace.globalPlace k F (directFactorPlace k F p P))) :
    functionFieldDifferentialTrace (k := k) (F := F) omega ∈
      Differential.localDifferentialLattice (GlobalPlace.rationalAdic p) := by
  classical
  by_cases homega_ne : omega ≠ 0
  · obtain ⟨t, ht, htorder⟩ :=
      DirectSemilocalUniformizer.exists_directSemilocalUniformizer k F p
    let tf : F := algebraMap (B k F) F t
    have htf_ne : tf ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (B k F) F)).mpr ht
    let Q : p.asIdeal.primesOver (B k F) := Classical.choice inferInstance
    have hQ_normalized : (Q : Ideal (B k F)) ∈ normalizedFactors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) :=
      (Ideal.mem_primesOver_iff_mem_normalizedFactors
        (B k F) p.ne_bot).mp Q.property
    have hQ_factor : (Q : Ideal (B k F)) ∈ factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) := by
      simpa only [factors_eq_normalizedFactors] using hQ_normalized
    let P₀ : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset :=
      ⟨(Q : Ideal (B k F)), Multiset.mem_toFinset.mpr hQ_factor⟩
    have hlog_ne : Differential.logarithmicDifferential
        (k := k) (F := F) tf ≠ 0 :=
      logarithmicDifferential_ne_zero_of_order_eq_one k F
        (AffinePlace.globalPlace k F (directFactorPlace k F p P₀))
        tf htf_ne (htorder P₀)
    have hdt_ne : differential k F tf ≠ 0 := by
      rw [differential_eq_smul_logarithmicDifferential k F tf htf_ne]
      exact smul_ne_zero htf_ne hlog_ne
    let C : Differential k F →ₗ[F] F :=
      functionFieldDifferentialCoordinate (k := k) (F := F)
    have hComega_ne : C omega ≠ 0 :=
      (functionFieldDifferentialCoordinate_ne_zero_iff
        (k := k) (F := F) omega).mpr homega_ne
    have hCdt_ne : C (differential k F tf) ≠ 0 :=
      (functionFieldDifferentialCoordinate_ne_zero_iff
        (k := k) (F := F) (differential k F tf)).mpr hdt_ne
    let c : F := C omega * (C (differential k F tf))⁻¹
    have hc_ne : c ≠ 0 :=
      mul_ne_zero hComega_ne (inv_ne_zero hCdt_ne)
    have homega_eq : omega = c • differential k F tf := by
      apply (functionFieldDifferentialEquiv (k := k) (F := F)).injective
      change C omega = C (c • differential k F tf)
      rw [map_smul]
      change C omega = (C omega * (C (differential k F tf))⁻¹) *
        C (differential k F tf)
      rw [mul_assoc, inv_mul_cancel₀ hCdt_ne, mul_one]
    have hc_regular : ∀ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        GlobalPlace.RegularAt
          (AffinePlace.globalPlace k F (directFactorPlace k F p P)) c := by
      intro P
      let Pplace : GlobalPlace k F :=
        AffinePlace.globalPlace k F (directFactorPlace k F p P)
      have homega_order : 0 ≤ differentialOrder
          (k := k) (F := F) Pplace omega homega_ne :=
        (Differential.mem_localDifferentialLattice_iff_differentialOrder_nonnegative
          (k := k) (F := F) Pplace omega homega_ne).mp (homega P)
      have hdt_order : differentialOrder
          (k := k) (F := F) Pplace (differential k F tf) hdt_ne = 0 :=
        differentialOrder_differential_eq_zero_of_order_eq_one
          k F Pplace tf htf_ne (htorder P) hdt_ne
      apply (GlobalPlace.regularAt_iff_order_nonnegative Pplace hc_ne).mpr
      have hc_order : Pplace.order c =
          differentialOrder
            (k := k) (F := F) Pplace omega homega_ne := by
        change Pplace.order
            (C omega * (C (differential k F tf))⁻¹) =
          Pplace.order (C omega) -
            FunctionFieldDifferential.localDerivativeLatticeGeneratorOrder
              (k := k) (F := F) Pplace
        rw [GlobalPlace.order_mul Pplace hComega_ne (inv_ne_zero hCdt_ne),
          GlobalPlace.order_inv]
        change Pplace.order (C (differential k F tf)) -
            FunctionFieldDifferential.localDerivativeLatticeGeneratorOrder
              (k := k) (F := F) Pplace = 0 at hdt_order
        omega
      rw [hc_order]
      exact homega_order
    obtain ⟨a, ha, b, hb⟩ :=
      DirectSemilocalDenominator.exists_directSemilocal_integral_multiple
        k F p c hc_regular
    let aK : RatFunc k := algebraMap (R k) (RatFunc k) a
    have ha_ne : a ≠ 0 := by
      intro hzero
      apply ha
      rw [hzero]
      exact p.asIdeal.zero_mem
    have haK_ne : aK ≠ 0 := RatFunc.algebraMap_ne_zero ha_ne
    have hinput : aK • omega =
        algebraMap (B k F) F b • differential k F tf := by
      rw [← IsScalarTower.algebraMap_smul F aK omega]
      rw [homega_eq, smul_smul]
      dsimp only [aK]
      rw [← IsScalarTower.algebraMap_apply (R k) (RatFunc k) F a, ← hb]
    have hscaled : aK •
        functionFieldDifferentialTrace (k := k) (F := F) omega ∈
          Differential.localDifferentialLattice
            (GlobalPlace.rationalAdic p) := by
      have hintegral :=
        functionFieldDifferentialTrace_directIntegral_smul_differential_mem_rationalAdic
          k F p b t
      have htrace : aK •
          functionFieldDifferentialTrace (k := k) (F := F) omega =
        functionFieldDifferentialTrace (k := k) (F := F)
          (algebraMap (B k F) F b • differential k F tf) := by
        calc
          aK • functionFieldDifferentialTrace (k := k) (F := F) omega =
              functionFieldDifferentialTrace (k := k) (F := F)
                (aK • omega) :=
            ((functionFieldDifferentialTrace (k := k) (F := F)).map_smul
              aK omega).symm
          _ = functionFieldDifferentialTrace (k := k) (F := F)
                (algebraMap (B k F) F b • differential k F tf) := by
            rw [hinput]
      rw [htrace]
      simpa only [tf] using hintegral
    have haVal : p.valuation (RatFunc k) aK = 1 := by
      exact (p.valuation_eq_one_iff_notMem (K := RatFunc k)).mpr ha
    let ainv : (GlobalPlace.rationalAdic p).valuationRing :=
      ⟨aK⁻¹, by
        change p.valuation (RatFunc k) aK⁻¹ ≤ 1
        rw [map_inv₀, haVal, inv_one]⟩
    have hunscaled :=
      (Differential.localDifferentialLattice (GlobalPlace.rationalAdic p)).smul_mem
        ainv hscaled
    change aK⁻¹ •
        (aK • functionFieldDifferentialTrace (k := k) (F := F) omega) ∈
      Differential.localDifferentialLattice (GlobalPlace.rationalAdic p) at hunscaled
    simpa only [smul_smul, inv_mul_cancel₀ haK_ne, one_smul] using hunscaled
  · have homega_zero : omega = 0 := Classical.not_not.mp homega_ne
    subst omega
    rw [map_zero]
    exact (Differential.localDifferentialLattice
      (GlobalPlace.rationalAdic p)).zero_mem
end QEC.Coding.AlgebraicGeometry.DirectSemilocalDifferentialTraceRegularity
