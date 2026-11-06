-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.agEvaluation_pairing_eq_zero_of_residue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:25:55.96277+00:00
-- url     : https://prove2.me/submissions/3c2fb9ff-2d0f-4283-922d-06c5688c97c7

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ResiduePairing
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_Rational_constantsToResidue_bijective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_eq_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_smul_mem_localDifferentialLattice_iff_order_add_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_mem_support_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_riemannRochSubmodule_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_constantsToResidue_bijective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluationLinearMap_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agWordStar_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationDivisor_apply_at
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_zeroCoordinateDivisor_apply_eq_zero_of_not_mem
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



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open FunctionFieldDifferential
noncomputable section
variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.residuePairingConstantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.residuePairingConstantTower
variable {ι : Type*} [Fintype ι]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (G H : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (hH : ∀ j, H (Q j).place = 0)
    (eta : Differential k F) (heta : eta ≠ 0)
    (etaAt : ∀ j, Differential.simplePoleDifferentialLattice (Q j).place)
    (hAt : ∀ j, (etaAt j : Differential k F) = eta)
    (hres : ∀ j, Differential.simplePoleResidue (Q j).place (etaAt j) = 1)
    (hGH : G + H ≤ differentialDivisor eta heta + evaluationDivisor Q)
    (x : GlobalPlace.riemannRochSubmodule G)
    (y : GlobalPlace.riemannRochSubmodule H) :
    wordPairing (agEvaluationLinearMap G Q hG x) (agEvaluationLinearMap H Q hH y) = 0 := by
  classical
  by_cases hx : (x : F) = 0
  · have hx0 : x = 0 := Subtype.ext hx
    simp [hx0, wordPairing]
  by_cases hy : (y : F) = 0
  · have hy0 : y = 0 := Subtype.ext hy
    simp [hy0, wordPairing]
  have hxy : (x : F) * (y : F) ≠ 0 := mul_ne_zero hx hy
  have hDzero (P : GlobalPlace k F) (hP : ¬ ∃ j, (Q j).place = P) :
      evaluationDivisor Q P = 0 := by
    exact zeroCoordinateDivisor_apply_eq_zero_of_not_mem Q Finset.univ P
      (fun j _ hj => hP ⟨j, hj⟩)
  have hDle (P : GlobalPlace k F) : evaluationDivisor Q P ≤ 1 := by
    by_cases hP : ∃ j, (Q j).place = P
    · obtain ⟨j, rfl⟩ := hP
      rw [evaluationDivisor_apply_at Q hQ]
    · rw [hDzero P hP]
      norm_num
  have horder (P : GlobalPlace k F) :
      -(evaluationDivisor Q P) ≤
        P.order ((x : F) * (y : F)) + differentialOrder P eta heta := by
    have hxP := (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative G hx).mp
      x.property P
    have hyP := (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative H hy).mp
      y.property P
    have h := hGH P
    simp only [Finsupp.add_apply, differentialDivisor_apply] at h
    rw [GlobalPlace.order_mul P hx hy]
    omega
  let omega : Differential k F := ((x : F) * (y : F)) • eta
  have homega : Differential.IsGlobalSimplePole omega := by
    intro P
    apply (Differential.smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
      P ((x : F) * (y : F)) hxy eta heta).mpr
    exact le_trans (neg_le_neg (hDle P)) (horder P)
  have hregular (P : GlobalPlace k F) (hP : ¬ ∃ j, (Q j).place = P) :
      omega ∈ Differential.localDifferentialLattice P := by
    apply (Differential.smul_mem_localDifferentialLattice_iff_order_add_nonnegative
      P ((x : F) * (y : F)) hxy eta heta).mpr
    have h := horder P
    simpa only [hDzero P hP, neg_zero] using h
  let residues := Differential.globalSimplePoleResidue omega homega
  have hcoefficient (j : ι) : residues (Q j).place =
      agEvaluationLinearMap G Q hG x j * agEvaluationLinearMap H Q hH y j := by
    let P := (Q j).place
    letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
    letI : FiniteDimensional k P.residueField := GlobalPlace.residueField_finiteDimensional P
    have hxReg : GlobalPlace.RegularAt P (x : F) := by
      have h := (GlobalPlace.mem_riemannRochSubmodule_iff G (x : F)).mp x.property P
      have hport := h
      simp only [P, hG j, WithZero.exp_zero] at hport ⊢
      exact hport
    have hyReg : GlobalPlace.RegularAt P (y : F) := by
      have h := (GlobalPlace.mem_riemannRochSubmodule_iff H (y : F)).mp y.property P
      have hport := h
      simp only [P, hH j, WithZero.exp_zero] at hport ⊢
      exact hport
    let xO : P.valuationRing := ⟨x, (GlobalPlace.mem_valuationRing_iff P _).mpr hxReg⟩
    let yO : P.valuationRing := ⟨y, (GlobalPlace.mem_valuationRing_iff P _).mpr hyReg⟩
    let xyO : P.valuationRing := xO * yO
    have hsub : (⟨omega, homega P⟩ : Differential.simplePoleDifferentialLattice P) =
        xyO • etaAt j := by
      apply Subtype.ext
      change ((x : F) * (y : F)) • eta = ((x : F) * (y : F)) • (etaAt j : Differential k F)
      rw [hAt]
    have hresProduct : Differential.simplePoleResidue P ⟨omega, homega P⟩ = P.residue xyO := by
      rw [hsub, Differential.simplePoleResidue_smul, hres, mul_one]
    have heval : P.residue xyO = algebraMap k P.residueField ((Q j).evaluate xyO) := by
      symm
      change P.constantsToResidue ((Q j).evaluate xyO) = P.residue xyO
      rw [← (Q j).constantsEquiv_apply]
      exact (Q j).constantsEquiv.apply_symm_apply _
    have hfinrank : Module.finrank k P.residueField = 1 := by
      apply Module.finrank_of_bijective_algebraMap
      exact (Q j).constantsToResidue_bijective
    change Algebra.trace k P.residueField
      (Differential.simplePoleResidue P ⟨omega, homega P⟩) = _
    rw [hresProduct, heval, Algebra.trace_algebraMap, hfinrank, one_smul]
    change (Q j).evaluate (xO * yO) = _
    rw [map_mul]
    rfl
  have hsupport : residues.support ⊆ Finset.univ.image (fun j => (Q j).place) := by
    intro P hP
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    by_contra hnot
    have hz := Differential.simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
      P omega (homega P) (hregular P hnot)
    exact Finsupp.mem_support_iff.mp hP hz
  have hsum : residues.sum (fun _ c => c) = ∑ j : ι, residues (Q j).place := by
    rw [Finsupp.sum_of_support_subset residues hsupport (fun _ c => c) (fun _ _ => rfl)]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hQ hab
  have hz := Differential.globalSimplePoleResidueSum_eq_zero (k := k) (F := F) omega homega
  change residues.sum (fun _ c => c) = 0 at hz
  rw [hsum] at hz
  change (∑ j : ι, agEvaluationLinearMap G Q hG x j * agEvaluationLinearMap H Q hH y j) = 0
  simpa only [hcoefficient] using hz
end QEC.Coding.AlgebraicGeometry
