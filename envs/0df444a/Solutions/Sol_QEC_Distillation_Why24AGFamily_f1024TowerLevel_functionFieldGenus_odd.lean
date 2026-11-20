-- Prove2me | solution 1 for QEC.Distillation.Why24AGFamily.f1024TowerLevel_functionFieldGenus_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:20:56.046369+00:00
-- url     : https://prove2.me/submissions/699752f2-ae78-4d3c-ba31-95e34684aead

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
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_CanonicalDivisor_degree_eq_two_mul_genus_sub_two
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_coe
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
private theorem f1024TowerLevelCanonicalDegree_reverseOddSum (m : ℕ) :
    (∑ i : Fin m,
        (31 : ℤ) * (32 : ℤ) ^ (2 * m - (i : ℕ))) =
      (32 : ℤ) ^ (m + 1) * ((32 : ℤ) ^ m - 1) := by
  calc
    (∑ i : Fin m,
        (31 : ℤ) * (32 : ℤ) ^ (2 * m - (i : ℕ))) =
        ∑ j : Fin m, (31 : ℤ) * (32 : ℤ) ^ (m + 1 + (j : ℕ)) := by
      apply Fintype.sum_equiv Fin.revPerm
      intro i
      apply congrArg (fun n : ℕ => (31 : ℤ) * (32 : ℤ) ^ n)
      simp only [Fin.revPerm_apply]
      change 2 * m - (i : ℕ) = m + 1 + (m - ((i : ℕ) + 1))
      omega
    _ = (32 : ℤ) ^ (m + 1) *
        ∑ j : Fin m, (31 : ℤ) * (32 : ℤ) ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro j
      rw [pow_add]
      ring
    _ = (32 : ℤ) ^ (m + 1) * ((32 : ℤ) ^ m - 1) := by
      rw [f1024TowerLevelCanonicalDegree_geometricSum]
private theorem f1024TowerLevelCanonicalDegreeArithmetic_odd (m : ℕ) :
    ((32 : ℤ) ^ (2 * m + 2) - 34) +
        ∑ i : Fin (m + 1),
          (34 * ((32 : ℤ) ^ (2 * m + 1 - (2 * (i : ℕ) + 1)) - 1)) *
            (31 * (32 : ℤ) ^ (i : ℕ)) =
      66 * (32 : ℤ) ^ (2 * m + 1) - 1122 * (32 : ℤ) ^ m := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have hlast :
      (34 * ((32 : ℤ) ^ (2 * m + 1 - (2 * m + 1)) - 1)) *
          (31 * (32 : ℤ) ^ m) = 0 := by
    norm_num
  rw [hlast, add_zero]
  have hsum :
      (∑ i : Fin m,
          (34 * ((32 : ℤ) ^ (2 * m + 1 - (2 * (i : ℕ) + 1)) - 1)) *
            (31 * (32 : ℤ) ^ (i : ℕ))) =
        34 *
          ((∑ i : Fin m,
              (31 : ℤ) * (32 : ℤ) ^ (2 * m - (i : ℕ))) -
            ∑ i : Fin m, (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
    calc
      (∑ i : Fin m,
          (34 * ((32 : ℤ) ^ (2 * m + 1 - (2 * (i : ℕ) + 1)) - 1)) *
            (31 * (32 : ℤ) ^ (i : ℕ))) =
          ∑ i : Fin m,
            34 *
              ((31 : ℤ) * (32 : ℤ) ^ (2 * m - (i : ℕ)) -
                (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
        apply Fintype.sum_congr
        intro i
        have hexponent :
            2 * m + 1 - (2 * (i : ℕ) + 1) + (i : ℕ) =
              2 * m - (i : ℕ) := by
          omega
        calc
          (34 * ((32 : ℤ) ^ (2 * m + 1 - (2 * (i : ℕ) + 1)) - 1)) *
                (31 * (32 : ℤ) ^ (i : ℕ)) =
              34 *
                (31 * ((32 : ℤ) ^ (2 * m + 1 - (2 * (i : ℕ) + 1)) *
                    (32 : ℤ) ^ (i : ℕ)) -
                  31 * (32 : ℤ) ^ (i : ℕ)) := by ring
          _ = 34 *
              ((31 : ℤ) * (32 : ℤ) ^ (2 * m - (i : ℕ)) -
                (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
            rw [← pow_add, hexponent]
      _ = 34 *
          ((∑ i : Fin m,
              (31 : ℤ) * (32 : ℤ) ^ (2 * m - (i : ℕ))) -
            ∑ i : Fin m, (31 : ℤ) * (32 : ℤ) ^ (i : ℕ)) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum, f1024TowerLevelCanonicalDegree_reverseOddSum,
    f1024TowerLevelCanonicalDegree_geometricSum]
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, pow_succ,
    show m + 1 = m + 1 by rfl, pow_succ]
  ring_nf
private theorem f1024TowerLevelCanonicalDivisor_degree_odd (r : ℕ) :
    Divisor.degree
        (QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 3)))
        (f1024TowerLevelCanonicalDivisor (2 * r + 3)) =
      66 * (32 : ℤ) ^ (2 * r + 3) - 1122 * (32 : ℤ) ^ (r + 1) := by
  rw [f1024TowerLevelCanonicalDivisor_degree_expansion]
  rw [show 2 * r + 3 + 1 = 2 * (r + 1) + 2 by omega]
  rw [show (2 * (r + 1) + 2) / 2 = (r + 1) + 1 by omega]
  rw [show 2 * r + 3 = 2 * (r + 1) + 1 by omega]
  exact f1024TowerLevelCanonicalDegreeArithmetic_odd (r + 1)
private theorem f1024TowerLevel_evenGenus_subtrahend_le (r : ℕ) :
    561 * 32 ^ (r + 1) ≤ 33 * 32 ^ (2 * r + 3) := by
  let q := 32 ^ (r + 1)
  have hpower : 32 ≤ q := by
    dsimp only [q]
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 32)
      (by omega : 1 ≤ r + 1)
    norm_num at h ⊢
    exact h
  have hbig : 32 ^ (2 * r + 3) = q * q * 32 := by
    dsimp only [q]
    rw [show 2 * r + 3 = (r + 1) + (r + 1) + 1 by omega,
      pow_add, pow_add]
    norm_num
  change 561 * q ≤ 33 * 32 ^ (2 * r + 3)
  rw [hbig]
  have hmul : q * 32 ≤ q * q := Nat.mul_le_mul_left q hpower
  nlinarith
private theorem f1024TowerLevel_evenGenus_cast (r : ℕ) :
    (evenGenus r : ℤ) =
      33 * (32 : ℤ) ^ (2 * r + 3) -
        561 * (32 : ℤ) ^ (r + 1) + 1 := by
  rw [evenGenus, Nat.cast_add,
    Nat.cast_sub (f1024TowerLevel_evenGenus_subtrahend_le r)]
  norm_num
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
open QEC.Coding.AlgebraicGeometry
attribute [local instance] QEC.Distillation.Why24AGFamily.f1024TowerLevelCoordinateDivisorAlgebraInst
attribute [local instance] QEC.Distillation.Why24AGFamily.f1024TowerLevelCoordinateDivisorRationalScalarTowerInst
attribute [local instance] QEC.Distillation.Why24AGFamily.f1024TowerLevelCoordinateDivisorStepConstantScalarTower
attribute [local instance] QEC.Distillation.Why24AGFamily.f1024TowerLevelCoordinateDivisorAlgebraInst QEC.Distillation.Why24AGFamily.f1024TowerLevelCoordinateDivisorRationalScalarTowerInst QEC.Distillation.Why24AGFamily.f1024TowerLevelCoordinateDivisorStepConstantScalarTower
namespace QEC.Distillation.Why24AGFamily
theorem _root_.solution (r : ℕ) :
    QEC.Coding.AlgebraicGeometry.GlobalPlace.functionFieldGenus F1024
        (F1024TowerLevel (2 * r + 3)) = evenGenus r := by
  apply Nat.cast_injective (R := ℤ)
  rw [f1024TowerLevel_evenGenus_cast]
  have hcanonical :=
    QEC.Coding.AlgebraicGeometry.CanonicalDivisor.degree_eq_two_mul_genus_sub_two
      (k := F1024) (F := F1024TowerLevel (2 * r + 3))
      (f1024TowerLevelCanonicalDivisor_isCanonical (2 * r + 3))
  rw [f1024TowerLevelCanonicalDivisor_degree_odd] at hcanonical
  omega
end QEC.Distillation.Why24AGFamily
