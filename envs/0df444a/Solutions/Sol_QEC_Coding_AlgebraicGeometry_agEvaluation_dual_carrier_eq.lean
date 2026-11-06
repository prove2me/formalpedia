-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.agEvaluation_dual_carrier_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:15:57.871391+00:00
-- url     : https://prove2.me/submissions/6628b5af-d5ba-4b52-b173-319776bdf428

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_Rational_constantsToResidue_bijective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_eq_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_smul_mem_localDifferentialLattice_iff_order_add_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_mem_support_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_coe
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_riemannRochSubmodule_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRoch_correction_term
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationDivisor_degree_eq_card
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
import Theorems.Thm_QEC_Coding_LinearCode_dimension_add_dual_dimension_eq_length
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
namespace QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithTop WithZero
noncomputable section
variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] agCodeDualityAlgebra
attribute [local instance] agCodeDualityScalarTower
attribute [local instance] agCodeDualityFiniteDimensional
variable [IsFullConstantField k F]
variable {ι : Type*} [Fintype ι]
private theorem agEvaluationKernelRestriction_injective
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0) :
    Function.Injective
      (agEvaluationKernelRestriction (k := k) (F := F) G Q hQ hG) := by
  intro x y hxy
  have hval : ((x.1 : GlobalPlace.riemannRochSubmodule G) : F) =
      ((y.1 : GlobalPlace.riemannRochSubmodule G) : F) :=
    congrArg
      (fun z : GlobalPlace.riemannRochSubmodule (G - evaluationDivisor Q) =>
        (z : F)) hxy
  exact Subtype.ext (Subtype.ext hval)
private theorem agEvaluation_dimension_ge_riemannRoch_difference
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0) :
    (GlobalPlace.riemannRochDimension G : ℤ) -
        (GlobalPlace.riemannRochDimension (G - evaluationDivisor Q) : ℤ) ≤
      (QEC.Coding.Dimension (agEvaluationCode G Q hG) : ℤ) := by
  have hkerNat : Module.finrank k (agEvaluationLinearMap G Q hG).ker ≤
      Module.finrank k
        (GlobalPlace.riemannRochSubmodule (G - evaluationDivisor Q)) :=
    LinearMap.finrank_le_finrank_of_injective
      (agEvaluationKernelRestriction_injective
        (k := k) (F := F) G Q hQ hG)
  have hker : (Module.finrank k (agEvaluationLinearMap G Q hG).ker : ℤ) ≤
      (GlobalPlace.riemannRochDimension (G - evaluationDivisor Q) : ℤ) := by
    exact_mod_cast hkerNat
  have hrankNat := (agEvaluationLinearMap G Q hG).finrank_range_add_finrank_ker
  have hrank := congrArg (fun n : ℕ => (n : ℤ)) hrankNat
  simp only [Nat.cast_add] at hrank
  change (GlobalPlace.riemannRochDimension G : ℤ) -
      (GlobalPlace.riemannRochDimension (G - evaluationDivisor Q) : ℤ) ≤
    (Module.finrank k (agEvaluationLinearMap G Q hG).range : ℤ)
  change (Module.finrank k (agEvaluationLinearMap G Q hG).range : ℤ) +
      (Module.finrank k (agEvaluationLinearMap G Q hG).ker : ℤ) =
    (GlobalPlace.riemannRochDimension G : ℤ) at hrank
  omega
variable [Nonempty ι]
private theorem normalizedEvaluationProduct_mem_localDifferentialLattice_of_not_selected
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F))
    (x : GlobalPlace.riemannRochSubmodule G)
    (y : GlobalPlace.riemannRochSubmodule
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G))
    (P : GlobalPlace k F) (hP : ¬ ∃ i, (Q i).place = P) :
    ((x : F) * (y : F)) • normalizedEvaluationDifferential
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ ∈
      Differential.localDifferentialLattice P := by
  by_cases hx : (x : F) = 0
  · simp only [hx, zero_mul, zero_smul]
    exact (Differential.localDifferentialLattice P).zero_mem
  by_cases hy : (y : F) = 0
  · simp only [hy, mul_zero, zero_smul]
    exact (Differential.localDifferentialLattice P).zero_mem
  have hxy : (x : F) * (y : F) ≠ 0 := mul_ne_zero hx hy
  apply (Differential.smul_mem_localDifferentialLattice_iff_order_add_nonnegative
    (k := k) (F := F) P ((x : F) * (y : F)) hxy
    (normalizedEvaluationDifferential
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
    (normalizedEvaluationDifferential_ne_zero
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)).mpr
  rw [GlobalPlace.order_mul P hx hy]
  have hxP :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative G hx).mp
      x.property P
  have hyP :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G) hy).mp
      y.property P
  have hD : evaluationDivisor Q P = 0 := by
    simpa only [evaluationDivisor] using
      zeroCoordinateDivisor_apply_eq_zero_of_not_mem Q Finset.univ P (by
        intro i _ hplace
        exact hP ⟨i, hplace⟩)
  simp only [normalizedEvaluationDualDivisor, Finsupp.sub_apply,
    Finsupp.add_apply, normalizedEvaluationCanonicalDivisor,
    FunctionFieldDifferential.differentialDivisor_apply, hD, add_zero] at hyP
  omega
private theorem simplePoleTraceResidue_rational_eq_coordinate
    (Q : RationalPlace k F) (omega : Differential k F)
    (homega : omega ∈ Differential.simplePoleDifferentialLattice Q.place) :
    Differential.simplePoleTraceResidue (k := k) (F := F) Q.place omega homega =
      Q.constantsEquiv.symm
        (Differential.simplePoleResidue (k := k) (F := F) Q.place
          ⟨omega, homega⟩) := by
  letI : Algebra k Q.place.residueField := GlobalPlace.residueAlgebra Q.place
  letI : FiniteDimensional k Q.place.residueField :=
    GlobalPlace.residueField_finiteDimensional Q.place
  obtain ⟨c, hc⟩ := Q.constantsEquiv.surjective
    (Differential.simplePoleResidue (k := k) (F := F) Q.place ⟨omega, homega⟩)
  change Algebra.trace k Q.place.residueField
      (Differential.simplePoleResidue (k := k) (F := F) Q.place
        ⟨omega, homega⟩) = _
  rw [← hc, Q.constantsEquiv_apply]
  have hconstants : Q.place.constantsToResidue c =
      algebraMap k Q.place.residueField c := by
    rfl
  rw [hconstants]
  rw [Algebra.trace_algebraMap]
  have hcoordinate :
      Q.constantsEquiv.symm (algebraMap k Q.place.residueField c) = c := by
    rw [← hconstants, ← Q.constantsEquiv_apply,
      Q.constantsEquiv.symm_apply_apply]
  have hfinrank : Module.finrank k Q.place.residueField = 1 := by
    apply Module.finrank_of_bijective_algebraMap
    simpa only [GlobalPlace.residueAlgebra, RingHom.algebraMap_toAlgebra] using
      Q.constantsToResidue_bijective
  rw [hfinrank, hcoordinate]
  simp
private theorem normalizedEvaluationProduct_traceResidue_at
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F)) (hG : ∀ i, G (Q i).place = 0)
    (x : GlobalPlace.riemannRochSubmodule G)
    (y : GlobalPlace.riemannRochSubmodule
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G))
    (i : ι) :
    Differential.simplePoleTraceResidue (k := k) (F := F) (Q i).place
        (((x : F) * (y : F)) • normalizedEvaluationDifferential
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
        (normalizedEvaluationProduct_isGlobalSimplePole
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G x y
          (Q i).place) =
      agEvaluationLinearMap G Q hG x i *
        agEvaluationLinearMap
          (normalizedEvaluationDualDivisor
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
          Q (normalizedEvaluationDualDivisor_apply_at
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G hG) y i := by
  let eta := normalizedEvaluationDifferential
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
  have hetaSimple : eta ∈
      Differential.simplePoleDifferentialLattice (Q i).place :=
    normalizedEvaluationDifferential_mem_simplePole
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i
  have hxRegular : GlobalPlace.RegularAt (Q i).place (x : F) := by
    have hxBound := (GlobalPlace.mem_riemannRochSubmodule_iff G (x : F)).mp
      x.property (Q i).place
    rw [hG i] at hxBound
    simpa only [GlobalPlace.RegularAt, WithZero.exp_zero] using hxBound
  have hyRegular : GlobalPlace.RegularAt (Q i).place (y : F) := by
    have hyBound := (GlobalPlace.mem_riemannRochSubmodule_iff
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G) (y : F)).mp
      y.property (Q i).place
    rw [normalizedEvaluationDualDivisor_apply_at
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G hG i] at hyBound
    simpa only [GlobalPlace.RegularAt, WithZero.exp_zero] using hyBound
  let xO : (Q i).place.valuationRing :=
    ⟨(x : F), (GlobalPlace.mem_valuationRing_iff (Q i).place _).mpr hxRegular⟩
  let yO : (Q i).place.valuationRing :=
    ⟨(y : F), (GlobalPlace.mem_valuationRing_iff (Q i).place _).mpr hyRegular⟩
  let xyO : (Q i).place.valuationRing := xO * yO
  rw [simplePoleTraceResidue_rational_eq_coordinate
    (k := k) (F := F) (Q i)]
  have hsubtype :
      (⟨((x : F) * (y : F)) • eta,
          normalizedEvaluationProduct_isGlobalSimplePole
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
            k F Q hQ G x y (Q i).place⟩ :
        Differential.simplePoleDifferentialLattice (Q i).place) =
      xyO • (⟨eta, hetaSimple⟩ :
        Differential.simplePoleDifferentialLattice (Q i).place) := by
    rfl
  rw [hsubtype, Differential.simplePoleResidue_smul, map_mul,
    normalizedEvaluationDifferential_residueCoordinate_eq_one
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ i,
    mul_one]
  change (Q i).evaluate xyO = _
  rw [show xyO = xO * yO by rfl, map_mul]
  rfl
private theorem normalizedEvaluationProduct_wordPairing_eq_zero
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F)) (hG : ∀ i, G (Q i).place = 0)
    (x : GlobalPlace.riemannRochSubmodule G)
    (y : GlobalPlace.riemannRochSubmodule
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)) :
    QEC.Coding.wordPairing
        (agEvaluationLinearMap
          (normalizedEvaluationDualDivisor
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
          Q (normalizedEvaluationDualDivisor_apply_at
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G hG) y)
        (agEvaluationLinearMap G Q hG x) = 0 := by
  classical
  let omega : Differential k F :=
    ((x : F) * (y : F)) • normalizedEvaluationDifferential
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
  let homega : Differential.IsGlobalSimplePole (k := k) (F := F) omega :=
    normalizedEvaluationProduct_isGlobalSimplePole
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G x y
  let residues : GlobalPlace k F →₀ k :=
    Differential.globalSimplePoleResidue (k := k) (F := F) omega homega
  have hsupport : residues.support ⊆
      Finset.univ.image (fun i => (Q i).place) := by
    intro P hP
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    by_contra hnotSelected
    have hregular : omega ∈ Differential.localDifferentialLattice P :=
      normalizedEvaluationProduct_mem_localDifferentialLattice_of_not_selected
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
        k F Q hQ G x y P hnotSelected
    have hzero :=
      Differential.simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
        (k := k) (F := F) P omega (homega P) hregular
    have hcoefficient : residues P = 0 := by
      change Differential.simplePoleTraceResidue
        (k := k) (F := F) P omega (homega P) = 0
      exact hzero
    exact (Finsupp.mem_support_iff.mp hP) hcoefficient
  have hsumSupport :
      residues.sum (fun _ coefficient => coefficient) =
        ∑ P ∈ Finset.univ.image (fun i => (Q i).place), residues P :=
    Finsupp.sum_of_support_subset residues hsupport
      (fun _ coefficient => coefficient) (fun _ _ => rfl)
  have hsumImage :
      (∑ P ∈ Finset.univ.image (fun i => (Q i).place), residues P) =
        ∑ i : ι, residues (Q i).place := by
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact hQ hij
  have hcoefficient (i : ι) :
      residues (Q i).place =
        agEvaluationLinearMap G Q hG x i *
          agEvaluationLinearMap
            (normalizedEvaluationDualDivisor
              (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
            Q (normalizedEvaluationDualDivisor_apply_at
              (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
              k F Q hQ G hG) y i := by
    change Differential.simplePoleTraceResidue (k := k) (F := F) (Q i).place
        (((x : F) * (y : F)) • normalizedEvaluationDifferential
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
        (normalizedEvaluationProduct_isGlobalSimplePole
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
          k F Q hQ G x y (Q i).place) = _
    exact normalizedEvaluationProduct_traceResidue_at
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
      k F Q hQ G hG x y i
  have hsumZero := Differential.globalSimplePoleResidueSum_eq_zero
    (k := k) (F := F) omega homega
  change residues.sum (fun _ coefficient => coefficient) = 0 at hsumZero
  change (∑ i : ι,
      agEvaluationLinearMap
          (normalizedEvaluationDualDivisor
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
          Q (normalizedEvaluationDualDivisor_apply_at
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
            k F Q hQ G hG) y i *
        agEvaluationLinearMap G Q hG x i) = 0
  calc
    _ = ∑ i : ι, agEvaluationLinearMap G Q hG x i *
        agEvaluationLinearMap
          (normalizedEvaluationDualDivisor
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
          Q (normalizedEvaluationDualDivisor_apply_at
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
            k F Q hQ G hG) y i := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = ∑ i : ι, residues (Q i).place := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hcoefficient i).symm
    _ = residues.sum (fun _ coefficient => coefficient) :=
      hsumImage.symm.trans hsumSupport.symm
    _ = 0 := hsumZero
private theorem normalizedEvaluationDualCode_le_dual
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (G : Divisor (GlobalPlace k F)) (hG : ∀ i, G (Q i).place = 0) :
    (agEvaluationCode
      (normalizedEvaluationDualDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
      Q (normalizedEvaluationDualDivisor_apply_at
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
        k F Q hQ G hG)).carrier ≤
      (agEvaluationCode G Q hG).dual.carrier := by
  intro dualWord hdualWord
  apply ((agEvaluationCode G Q hG).mem_dual dualWord).mpr
  intro word hword
  change dualWord ∈ (agEvaluationLinearMap
    (normalizedEvaluationDualDivisor
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
    Q (normalizedEvaluationDualDivisor_apply_at
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
      k F Q hQ G hG)).range at hdualWord
  change word ∈ (agEvaluationLinearMap G Q hG).range at hword
  obtain ⟨y, rfl⟩ := hdualWord
  obtain ⟨x, rfl⟩ := hword
  exact normalizedEvaluationProduct_wordPairing_eq_zero
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
    k F Q hQ G hG x y
end
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithTop WithZero
noncomputable section
variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.agCodeDualityAlgebra
attribute [local instance] agCodeDualityAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.agCodeDualityScalarTower
attribute [local instance] agCodeDualityScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.agCodeDualityFiniteDimensional
attribute [local instance] agCodeDualityFiniteDimensional
variable [IsFullConstantField k F]
variable {ι : Type*} [Fintype ι]
variable [Nonempty ι]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place)
    (hG : ∀ i, G (Q i).place = 0) :
    (agEvaluationCode G Q hG).dual.carrier =
      (agEvaluationCode
        (normalizedEvaluationDualDivisor
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G)
        Q (normalizedEvaluationDualDivisor_apply_at
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
          k F Q hQ G hG)).carrier := by
  let D := evaluationDivisor Q
  let K := normalizedEvaluationCanonicalDivisor
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ
  let H := normalizedEvaluationDualDivisor
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ G
  let hH : ∀ i, H (Q i).place = 0 :=
    normalizedEvaluationDualDivisor_apply_at
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
      k F Q hQ G hG
  change (agEvaluationCode G Q hG).dual.carrier =
    (agEvaluationCode H Q hH).carrier
  have hinclusion : (agEvaluationCode H Q hH).carrier ≤
      (agEvaluationCode G Q hG).dual.carrier :=
    normalizedEvaluationDualCode_le_dual
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
      k F Q hQ G hG
  symm
  apply Submodule.eq_of_le_of_finrank_eq hinclusion
  apply Nat.le_antisymm
  · exact Submodule.finrank_mono hinclusion
  · change QEC.Coding.Dimension (agEvaluationCode G Q hG).dual ≤
      QEC.Coding.Dimension (agEvaluationCode H Q hH)
    have hHLower := agEvaluation_dimension_ge_riemannRoch_difference
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
      k F H Q hQ hH
    have hGLower := agEvaluation_dimension_ge_riemannRoch_difference
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
      k F G Q hQ hG
    change (GlobalPlace.riemannRochDimension H : ℤ) -
        (GlobalPlace.riemannRochDimension (H - D) : ℤ) ≤
      (QEC.Coding.Dimension (agEvaluationCode H Q hH) : ℤ) at hHLower
    change (GlobalPlace.riemannRochDimension G : ℤ) -
        (GlobalPlace.riemannRochDimension (G - D) : ℤ) ≤
      (QEC.Coding.Dimension (agEvaluationCode G Q hG) : ℤ) at hGLower
    have hH_eq : H = K + D - G := by rfl
    have hH_sub_D : H - D = K - G := by
      rw [hH_eq]
      abel
    have hK_sub_G_sub_D : K - (G - D) = H := by
      rw [hH_eq]
      abel
    rw [hH_sub_D] at hHLower
    have hcorrectionG := GlobalPlace.riemannRoch_correction_term
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
      (normalizedEvaluationDifferential
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
      (normalizedEvaluationDifferential_ne_zero
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) G
    have hcorrectionGD := GlobalPlace.riemannRoch_correction_term
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
      (normalizedEvaluationDifferential
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
      (normalizedEvaluationDifferential_ne_zero
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
      (G - D)
    change (GlobalPlace.riemannRochDimension G : ℤ) -
        (GlobalPlace.riemannRochDimension (K - G) : ℤ) =
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G + 1 -
        (GlobalPlace.functionFieldGenus
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ)
      at hcorrectionG
    change (GlobalPlace.riemannRochDimension (G - D) : ℤ) -
        (GlobalPlace.riemannRochDimension (K - (G - D)) : ℤ) =
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) (G - D) + 1 -
        (GlobalPlace.functionFieldGenus
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ)
      at hcorrectionGD
    rw [hK_sub_G_sub_D] at hcorrectionGD
    have hdegreeD :
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) D =
          Fintype.card ι := by
      exact evaluationDivisor_degree_eq_card Q
    have hdegreeGD :
        Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) (G - D) =
          Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G -
            Fintype.card ι := by
      rw [Divisor.degree_sub, hdegreeD]
    rw [hdegreeGD] at hcorrectionGD
    have hsumNat :=
      (agEvaluationCode G Q hG).dimension_add_dual_dimension_eq_length
    change QEC.Coding.Dimension (agEvaluationCode G Q hG) +
        QEC.Coding.Dimension (agEvaluationCode G Q hG).dual =
      Fintype.card ι at hsumNat
    have hsum := congrArg (fun n : ℕ => (n : ℤ)) hsumNat
    simp only [Nat.cast_add] at hsum
    have hdualLe :
        (QEC.Coding.Dimension (agEvaluationCode G Q hG).dual : ℤ) ≤
          (QEC.Coding.Dimension (agEvaluationCode H Q hH) : ℤ) := by
      omega
    exact_mod_cast hdualLe
end QEC.Coding.AlgebraicGeometry
