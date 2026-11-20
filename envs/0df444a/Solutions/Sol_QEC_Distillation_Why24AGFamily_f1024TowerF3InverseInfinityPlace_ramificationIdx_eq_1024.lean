-- Prove2me | solution 1 for QEC.Distillation.Why24AGFamily.f1024TowerF3InverseInfinityPlace_ramificationIdx_eq_1024
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:41:55.267835+00:00
-- url     : https://prove2.me/submissions/b2e5c4a9-89a0-4b46-9402-802d40e34e0a

import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Data.Fin.Rev
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Unramified.Dedekind
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_FullConstantField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_FibreDirectFactor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Definitions.Def_QEC_Coding_QuditQubitConversion_FiniteField
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily
import Theorems.Thm_QEC_Distillation_Why24AGFamily_f1024TowerF3_finrank_over_F1
import Theorems.Thm_QEC_Distillation_Why24AGFamily_f1024TowerV3_inverse_equation
import Theorems.Thm_QEC_Distillation_Why24AGFamily_f1024TowerV3_ne_zero
import Theorems.Thm_QEC_Distillation_Why24AGFamily_f1024TowerF3InverseInfinityPlace_order_x1
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_coe
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_infinityFibreEquivDirectFactors_apply_asIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluationLinearMap_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agWordStar_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondTransposeCode_iff
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_taggedCczTransport_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv_quotientResidueEquiv
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSmulIntoDifferentialSpace_coe
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.agWordStar_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_xCode
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_zCode
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary1
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary2
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondTransposeCode_iff
attribute [local simp] QEC.Coding.why24QuditZ_apply
attribute [local simp] QEC.Coding.why24U_apply
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock
attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.mem_coordinateSupport
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_apply
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.taggedCczTransport_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
namespace QEC.Distillation.Why24AGFamily
open QEC.Coding
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open scoped Polynomial.Bivariate WithZero
open Polynomial
noncomputable section
private theorem f1024TowerF3T1_ne_zero : f1024TowerF3T1 ≠ 0 := by
  rw [f1024TowerF3T1]
  exact (map_ne_zero_iff (algebraMap F1024TowerF2 F1024TowerF3)
    (algebraMap F1024TowerF2 F1024TowerF3).injective).mpr
      (inv_ne_zero f1024TowerX1_ne_zero)
private theorem f1024TowerF3W2_ne_zero : f1024TowerF3W2 ≠ 0 := by
  rw [f1024TowerF3W2]
  exact (map_ne_zero_iff (algebraMap F1024TowerF2 F1024TowerF3)
    (algebraMap F1024TowerF2 F1024TowerF3).injective).mpr f1024TowerW2_ne_zero
private theorem f1024TowerF3W2_inverse_equation : f1024TowerF3W2 ^ 32 +
    f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31 = f1024TowerF3T1 := by
  simpa only [f1024TowerF3W2, f1024TowerF3T1, map_add, map_mul, map_pow] using
    congrArg (algebraMap F1024TowerF2 F1024TowerF3)
      f1024TowerW2_inverse_equation
private theorem f1024TowerV3_inverse_equation_local : f1024TowerV3 ^ 32 +
    f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31 = f1024TowerF3W2 := by
  simpa only [f1024TowerF3W2, map_pow] using f1024TowerV3_inverse_equation
private theorem f1024TowerF3W2_inverse_valuation_data
    (ν : Valuation F1024TowerF3 ℤᵐ⁰) (E : ℕ) (hEpos : 0 < E)
    (hνt : ν f1024TowerF3T1 = WithZero.exp (-(E : ℤ))) :
    ∃ m : ℕ, E = 32 * m ∧
      ν f1024TowerF3W2 = WithZero.exp (-(m : ℤ)) := by
  have hw0 : ν f1024TowerF3W2 ≠ 0 :=
    (Valuation.ne_zero_iff ν).mpr f1024TowerF3W2_ne_zero
  let r : ℤ := WithZero.log (ν f1024TowerF3W2)
  have hνw : ν f1024TowerF3W2 = WithZero.exp r := by
    dsimp only [r]
    exact (WithZero.exp_log hw0).symm
  have hνw32 : ν (f1024TowerF3W2 ^ 32) = WithZero.exp ((32 : ℕ) • r) := by
    rw [map_pow, hνw, ← WithZero.exp_nsmul]
  have hνtw : ν (f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31) =
      WithZero.exp ((32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r) := by
    rw [map_mul, map_pow, map_pow, hνt, hνw,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  have hνsum : ν (f1024TowerF3W2 ^ 32 +
      f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31) =
      WithZero.exp (-(E : ℤ)) := by
    rw [f1024TowerF3W2_inverse_equation, hνt]
  rcases lt_trichotomy (ν (f1024TowerF3W2 ^ 32))
      (ν (f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31)) with hlt | heq | hgt
  · have hsum : ν (f1024TowerF3W2 ^ 32 +
        f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31) =
        ν (f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31) := by
      rw [Valuation.map_add_eq_of_lt_right ν hlt]
    rw [hsum, hνtw] at hνsum
    have hEq : (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r = -(E : ℤ) :=
      WithZero.exp_inj.mp hνsum
    have hltExp : (32 : ℕ) • r <
        (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r := by
      rw [← f1024Tower_exp_lt_exp, ← hνw32, ← hνtw]
      exact hlt
    simp only [nsmul_eq_mul] at hEq hltExp
    omega
  · have hsame : WithZero.exp ((32 : ℕ) • r) =
        WithZero.exp ((32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r) := by
      rw [← hνw32, ← hνtw]
      exact heq
    have hEq : (32 : ℕ) • r =
        (32 : ℕ) • (-(E : ℤ)) + (31 : ℕ) • r :=
      WithZero.exp_inj.mp hsame
    have hsumle : ν (f1024TowerF3W2 ^ 32 +
        f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31) ≤
        ν (f1024TowerF3W2 ^ 32) :=
      (map_add_le_max ν _ _).trans_eq (by rw [← heq, max_self])
    rw [hνsum, hνw32] at hsumle
    have hsmall : (32 : ℕ) • r < -(E : ℤ) := by
      have hEq' : (32 : ℤ) * r =
          (32 : ℤ) * (-(E : ℤ)) + (31 : ℤ) * r := by
        have hport := hEq
        simp only [nsmul_eq_mul] at hport ⊢
        exact hport
      have hsmall' : (32 : ℤ) * r < -(E : ℤ) := by
        omega
      have hport := hsmall'
      simp only [nsmul_eq_mul] at hport ⊢
      exact hport
    exfalso
    exact (not_lt_of_ge hsumle) (f1024Tower_exp_lt_exp.mpr hsmall)
  · have hsum : ν (f1024TowerF3W2 ^ 32 +
        f1024TowerF3T1 ^ 32 * f1024TowerF3W2 ^ 31) =
        ν (f1024TowerF3W2 ^ 32) := by
      rw [Valuation.map_add_eq_of_lt_left ν hgt]
    rw [hsum, hνw32] at hνsum
    have hEq : (32 : ℕ) • r = -(E : ℤ) := WithZero.exp_inj.mp hνsum
    have hrneg : r < 0 := by
      rw [nsmul_eq_mul] at hEq
      omega
    have hnonneg : 0 ≤ -r := by omega
    rw [nsmul_eq_mul] at hEq
    have hEq' : (E : ℤ) = 32 * (-r) := by omega
    have hcast : (((-r).toNat : ℕ) : ℤ) = -r :=
      Int.toNat_of_nonneg hnonneg
    have hEq'' : (E : ℤ) = (32 : ℤ) * (((-r).toNat : ℕ) : ℤ) := by
      rw [hcast]
      exact hEq'
    refine ⟨(-r).toNat, ?_, ?_⟩
    · exact_mod_cast hEq''
    · calc
        ν f1024TowerF3W2 = WithZero.exp r := hνw
        _ = WithZero.exp (-(((-r).toNat : ℕ) : ℤ)) := by
          congr 1
          rw [hcast]
          ring
private theorem f1024TowerV3_inverse_valuation_data
    (ν : Valuation F1024TowerF3 ℤᵐ⁰) (m : ℕ) (hmpos : 0 < m)
    (hνw : ν f1024TowerF3W2 = WithZero.exp (-(m : ℤ))) :
    ∃ n : ℕ, m = 32 * n ∧
      ν f1024TowerV3 = WithZero.exp (-(n : ℤ)) := by
  have hV0 : ν f1024TowerV3 ≠ 0 :=
    (Valuation.ne_zero_iff ν).mpr f1024TowerV3_ne_zero
  let s : ℤ := WithZero.log (ν f1024TowerV3)
  have hνV : ν f1024TowerV3 = WithZero.exp s := by
    dsimp only [s]
    exact (WithZero.exp_log hV0).symm
  have hνV32 : ν (f1024TowerV3 ^ 32) = WithZero.exp ((32 : ℕ) • s) := by
    rw [map_pow, hνV, ← WithZero.exp_nsmul]
  have hνwV : ν (f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31) =
      WithZero.exp ((32 : ℕ) • (-(m : ℤ)) + (31 : ℕ) • s) := by
    rw [map_mul, map_pow, map_pow, hνw, hνV,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  have hνsum : ν (f1024TowerV3 ^ 32 +
      f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31) =
      WithZero.exp (-(m : ℤ)) := by
    rw [f1024TowerV3_inverse_equation_local, hνw]
  rcases lt_trichotomy (ν (f1024TowerV3 ^ 32))
      (ν (f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31)) with hlt | heq | hgt
  · have hsum : ν (f1024TowerV3 ^ 32 +
        f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31) =
        ν (f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31) := by
      rw [Valuation.map_add_eq_of_lt_right ν hlt]
    rw [hsum, hνwV] at hνsum
    have hEq : (32 : ℕ) • (-(m : ℤ)) + (31 : ℕ) • s = -(m : ℤ) :=
      WithZero.exp_inj.mp hνsum
    have hltExp : (32 : ℕ) • s <
        (32 : ℕ) • (-(m : ℤ)) + (31 : ℕ) • s := by
      rw [← f1024Tower_exp_lt_exp, ← hνV32, ← hνwV]
      exact hlt
    simp only [nsmul_eq_mul] at hEq hltExp
    omega
  · have hsame : WithZero.exp ((32 : ℕ) • s) =
        WithZero.exp ((32 : ℕ) • (-(m : ℤ)) + (31 : ℕ) • s) := by
      rw [← hνV32, ← hνwV]
      exact heq
    have hEq : (32 : ℕ) • s =
        (32 : ℕ) • (-(m : ℤ)) + (31 : ℕ) • s :=
      WithZero.exp_inj.mp hsame
    have hsumle : ν (f1024TowerV3 ^ 32 +
        f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31) ≤
        ν (f1024TowerV3 ^ 32) :=
      (map_add_le_max ν _ _).trans_eq (by rw [← heq, max_self])
    rw [hνsum, hνV32] at hsumle
    have hsmall : (32 : ℕ) • s < -(m : ℤ) := by
      have hEq' : (32 : ℤ) * s =
          (32 : ℤ) * (-(m : ℤ)) + (31 : ℤ) * s := by
        have hport := hEq
        simp only [nsmul_eq_mul] at hport ⊢
        exact hport
      have hsmall' : (32 : ℤ) * s < -(m : ℤ) := by
        omega
      have hport := hsmall'
      simp only [nsmul_eq_mul] at hport ⊢
      exact hport
    exfalso
    exact (not_lt_of_ge hsumle) (f1024Tower_exp_lt_exp.mpr hsmall)
  · have hsum : ν (f1024TowerV3 ^ 32 +
        f1024TowerF3W2 ^ 32 * f1024TowerV3 ^ 31) =
        ν (f1024TowerV3 ^ 32) := by
      rw [Valuation.map_add_eq_of_lt_left ν hgt]
    rw [hsum, hνV32] at hνsum
    have hEq : (32 : ℕ) • s = -(m : ℤ) := WithZero.exp_inj.mp hνsum
    have hsneg : s < 0 := by
      rw [nsmul_eq_mul] at hEq
      omega
    have hnonneg : 0 ≤ -s := by omega
    rw [nsmul_eq_mul] at hEq
    have hEq' : (m : ℤ) = 32 * (-s) := by omega
    have hcast : (((-s).toNat : ℕ) : ℤ) = -s :=
      Int.toNat_of_nonneg hnonneg
    have hEq'' : (m : ℤ) = (32 : ℤ) * (((-s).toNat : ℕ) : ℤ) := by
      rw [hcast]
      exact hEq'
    refine ⟨(-s).toNat, ?_, ?_⟩
    · exact_mod_cast hEq''
    · calc
        ν f1024TowerV3 = WithZero.exp s := hνV
        _ = WithZero.exp (-(((-s).toNat : ℕ) : ℤ)) := by
          congr 1
          rw [hcast]
          ring
private theorem f1024TowerF3InverseInfinityPlace_ramification_bounds
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF3)) :
    0 < (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal ∧
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal ≤ 1024 := by
  let oldRationalAlgebra : Algebra F1024TowerF1 F1024TowerF3 := inferInstance
  let oldFunctionField : _root_.FunctionField F1024 F1024TowerF3 := inferInstance
  let oldSeparable : Algebra.IsSeparable F1024TowerF1 F1024TowerF3 := inferInstance
  letI : Algebra F1024TowerF1 F1024TowerF3 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3
  letI : Algebra F1024[X] F1024TowerF3 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3
  letI : @IsScalarTower F1024[X] F1024TowerF1 F1024TowerF3
      RatFunc.instSMulOfFractionRingPolynomial
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3).toSMul
      (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3).toSMul :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3
  letI : _root_.FunctionField F1024 F1024TowerF3 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField)
      F1024 F1024TowerF3
  letI : Algebra.IsSeparable F1024TowerF1 F1024TowerF3 :=
    QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
      F1024 F1024TowerF3
  let B : Type _ := _root_.FunctionField.ringOfIntegers F1024 F1024TowerF3
  letI : Module.IsTorsionFree F1024[X] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective F1024 F1024TowerF3)
  letI : Module.Finite F1024[X] B :=
    QEC.Coding.AlgebraicGeometry.AffinePlace.finite_ringOfIntegers F1024 F1024TowerF3
  letI : NoZeroSMulDivisors F1024[X] B :=
    ⟨fun {c x} hzero =>
      (Module.isTorsionFree_iff_smul_eq_zero.mp
        (inferInstance : Module.IsTorsionFree F1024[X] B)) c x hzero⟩
  letI : ((Polynomial.idealX F1024).asIdeal).IsMaximal := by
    simpa using (Polynomial.idealX F1024).isMaximal
  let e := QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors
    (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3
  let Q := e P
  have hQ : (Q : Ideal B) = P.1.asIdeal := by
    dsimp only [Q, e]
    exact QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable)
      F1024 F1024TowerF3 P
  let E : ℕ :=
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
      P.1.asIdeal
  have hEeq : E = (Polynomial.idealX F1024).asIdeal.ramificationIdx' (Q : Ideal B) := by
    dsimp only [E, QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime]
    rw [← hQ]
  have hEpos : 0 < E := by
    rw [hEeq]
    exact Nat.pos_of_ne_zero
      (Ideal.Factors.ramificationIdx_ne_zero (Polynomial.idealX F1024).asIdeal Q)
  have hfinrank : Module.finrank F1024TowerF1 F1024TowerF3 = 1024 := by
    calc
      Module.finrank F1024TowerF1 F1024TowerF3 =
          (letI : Algebra F1024TowerF1 F1024TowerF3 := oldRationalAlgebra
           Module.finrank F1024TowerF1 F1024TowerF3) := by
        symm
        exact @Algebra.finrank_eq_of_equiv_equiv
          F1024TowerF1 F1024TowerF3 _ _ oldRationalAlgebra
          F1024TowerF1 F1024TowerF3 _ _
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalAlgebra
            (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3)
          (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm.toRingEquiv
          (RingEquiv.refl F1024TowerF3) (by
            ext x
            change QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalMap
                (oldRationalAlgebra := oldRationalAlgebra) F1024 F1024TowerF3
                ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm x) =
              (@algebraMap F1024TowerF1 F1024TowerF3 _ _ oldRationalAlgebra) x
            change (@algebraMap F1024TowerF1 F1024TowerF3 _ _ oldRationalAlgebra)
                (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024
                  ((QEC.Coding.AlgebraicGeometry.InverseAffinePlace.rationalInvolution F1024).symm x)) =
              (@algebraMap F1024TowerF1 F1024TowerF3 _ _ oldRationalAlgebra) x
            simp)
      _ = 1024 := f1024TowerF3_finrank_over_F1
  have hEbound : E ≤ 1024 := by
    rw [hEeq]
    calc
      (Polynomial.idealX F1024).asIdeal.ramificationIdx' (Q : Ideal B) ≤
          Module.finrank F1024TowerF1 F1024TowerF3 :=
        Ideal.ramificationIdx_le_finrank B F1024TowerF1 F1024TowerF3 (Q : Ideal B)
      _ = 1024 := hfinrank
  exact ⟨hEpos, hEbound⟩
private theorem f1024TowerF3InverseInfinityPlace_local_data
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF3)) :
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
        P.1.asIdeal = 1024 ∧
      f1024TowerF3InverseInfinityOrder P
        (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2) = -32 ∧
      f1024TowerF3InverseInfinityOrder P f1024TowerV3 = 1 := by
  let E : ℕ :=
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
      P.1.asIdeal
  obtain ⟨hEpos, hEbound⟩ :=
    f1024TowerF3InverseInfinityPlace_ramification_bounds P
  have horderT : f1024TowerF3InverseInfinityOrder P f1024TowerF3T1 = (E : ℤ) := by
    change @QEC.Coding.AlgebraicGeometry.GlobalPlace.order F1024 F1024TowerF3 _ _ _
        f1024TowerF3DirectConstantAlgebra
        (f1024TowerF3InverseInfinityPlace P) f1024TowerF3T1 = _
    rw [f1024TowerF3T1, f1024TowerT1_def, map_inv₀,
      @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF3 _ _ _
        f1024TowerF3DirectConstantAlgebra
        (f1024TowerF3InverseInfinityPlace P) _]
    change -f1024TowerF3InverseInfinityOrder P
      (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX1) = (E : ℤ)
    rw [f1024TowerF3InverseInfinityPlace_order_x1]
    dsimp [E]
    ring
  let ν : Valuation F1024TowerF3 ℤᵐ⁰ :=
    @QEC.Coding.AlgebraicGeometry.GlobalPlace.valuation F1024 F1024TowerF3 _ _ _
      f1024TowerF3DirectConstantAlgebra
      (f1024TowerF3InverseInfinityPlace P)
  have hlog : WithZero.log (ν f1024TowerF3T1) = -(E : ℤ) := by
    change -WithZero.log (ν f1024TowerF3T1) = (E : ℤ) at horderT
    omega
  have hνt : ν f1024TowerF3T1 = WithZero.exp (-(E : ℤ)) := by
    have ht0 : ν f1024TowerF3T1 ≠ 0 :=
      (Valuation.ne_zero_iff ν).mpr f1024TowerF3T1_ne_zero
    calc
      ν f1024TowerF3T1 = WithZero.exp (WithZero.log (ν f1024TowerF3T1)) :=
        (WithZero.exp_log ht0).symm
      _ = WithZero.exp (-(E : ℤ)) := by rw [hlog]
  obtain ⟨m, hEm, hνw⟩ :=
    f1024TowerF3W2_inverse_valuation_data ν E hEpos hνt
  have hmpos : 0 < m := by omega
  obtain ⟨n, hmn, hνV⟩ :=
    f1024TowerV3_inverse_valuation_data ν m hmpos hνw
  have hn : n = 1 := by omega
  have hm : m = 32 := by omega
  have hE : E = 1024 := by omega
  have hνw32 : ν f1024TowerF3W2 = WithZero.exp (-(32 : ℤ)) := by
    simpa [hm] using hνw
  have hνV1 : ν f1024TowerV3 = WithZero.exp (-(1 : ℤ)) := by
    simpa [hn] using hνV
  have horderW : f1024TowerF3InverseInfinityOrder P f1024TowerF3W2 = 32 := by
    change -WithZero.log (ν f1024TowerF3W2) = 32
    rw [hνw32]
    norm_num
  have horderX2 : f1024TowerF3InverseInfinityOrder P
      (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2) = -32 := by
    calc
      f1024TowerF3InverseInfinityOrder P
          (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2) =
          f1024TowerF3InverseInfinityOrder P f1024TowerF3W2⁻¹ := by
        rw [f1024TowerF3W2, f1024TowerW2_def, map_inv₀, inv_inv]
      _ = -f1024TowerF3InverseInfinityOrder P f1024TowerF3W2 :=
        @QEC.Coding.AlgebraicGeometry.GlobalPlace.order_inv F1024 F1024TowerF3 _ _ _
          f1024TowerF3DirectConstantAlgebra
          (f1024TowerF3InverseInfinityPlace P) _
      _ = -32 := by rw [horderW]
  have horderV : f1024TowerF3InverseInfinityOrder P f1024TowerV3 = 1 := by
    change -WithZero.log (ν f1024TowerV3) = 1
    rw [hνV1]
    norm_num
  dsimp [E] at hE
  exact ⟨hE, horderX2, horderV⟩
attribute [instance] F1024TowerStageData.fieldInst
  F1024TowerStageData.rationalAlgebraInst
  F1024TowerStageData.finiteDimensionalInst
  F1024TowerStageData.separableInst
  F1024TowerStageData.constantAlgebraInst
  F1024TowerStageData.constantRationalTowerInst
  F1024TowerStageData.polynomialAlgebraInst
  F1024TowerStageData.polynomialRationalTowerInst
  F1024TowerStageData.charTwoInst
attribute [instance] F1024TowerFiniteChartData.commRingInst
  F1024TowerFiniteChartData.domainInst
  F1024TowerFiniteChartData.dedekindInst
  F1024TowerFiniteChartData.constantAlgebraInst
  F1024TowerFiniteChartData.actualAlgebraInst
  F1024TowerFiniteChartData.constantTowerInst
  F1024TowerFiniteChartData.fractionRingInst
section TowerCoordinateDivisors
open QEC.Coding.AlgebraicGeometry
variable (F : Type*) [Field F]
variable [π : Algebra F1024[X] F] [ρ : Algebra F1024TowerF1 F]
variable [τ : IsScalarTower F1024[X] F1024TowerF1 F]
variable [φ : _root_.FunctionField F1024 F]
variable [s : Algebra.IsSeparable F1024TowerF1 F]
end TowerCoordinateDivisors
section TowerLevelCoordinateDivisors
open QEC.Coding.AlgebraicGeometry
attribute [local instance] QEC.Distillation.Why24AGFamily.f1024TowerLevelCoordinateDivisorAlgebraInst QEC.Distillation.Why24AGFamily.f1024TowerLevelCoordinateDivisorRationalScalarTowerInst QEC.Distillation.Why24AGFamily.f1024TowerLevelCoordinateDivisorStepConstantScalarTower
end TowerLevelCoordinateDivisors
open QEC.Coding.AlgebraicGeometry
attribute [local instance 2000] QEC.Distillation.Why24AGFamily.f1024Why24OddDirectConstantAlgebra QEC.Distillation.Why24AGFamily.f1024Why24OddDirectConstantScalarTower
open QEC.Distillation.Why24WeightedTriorthogonalCSS
end
end QEC.Distillation.Why24AGFamily
end

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.Why24AGFamily
open QEC.Coding
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open scoped Polynomial.Bivariate WithZero
open Polynomial
noncomputable section
attribute [local instance] QEC.Distillation.Why24AGFamily.f1024CharTwo
attribute [local instance] QEC.Distillation.Why24AGFamily.f1024TowerF2CharTwo
attribute [local instance] QEC.Distillation.Why24AGFamily.f1024TowerF3CharTwo
namespace QEC.Distillation.Why24AGFamily
theorem _root_.solution
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF3)) :
    (QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityBasePrime F1024).ramificationIdx'
      P.1.asIdeal = 1024 :=
  (f1024TowerF3InverseInfinityPlace_local_data P).1
end QEC.Distillation.Why24AGFamily
