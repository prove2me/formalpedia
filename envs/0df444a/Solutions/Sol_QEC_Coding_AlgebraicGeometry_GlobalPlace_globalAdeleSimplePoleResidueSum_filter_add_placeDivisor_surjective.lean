-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSimplePoleResidueSum_filter_add_placeDivisor_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:39:04.59107+00:00
-- url     : https://prove2.me/submissions/8fc8ede1-337e-4565-8d75-fc78718682a1

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleWeilDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialResidue
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_uniformizerLogDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleTraceResidue_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_apply
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped BigOperators Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialResidueAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialResidueScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (omega : Differential k F) (homega : omega ≠ 0)
    (P : GlobalPlace k F) :
    Function.Surjective fun a : globalAdeleFilter (k := k) (F := F)
        (FunctionFieldDifferential.differentialDivisor
          (k := k) (F := F) omega homega + placeDivisor P) =>
      globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega
        ⟨(a : GlobalAdele (k := k) (F := F)),
          globalAdeleFilter_add_placeDivisor_le_globalAdeleSimplePoleSubmodule
            (k := k) (F := F) omega homega P a.property⟩ := by
  classical
  let K := FunctionFieldDifferential.differentialDivisor
    (k := k) (F := F) omega homega
  intro c
  by_cases hc : c = 0
  · subst c
    refine ⟨(0 : globalAdeleFilter (k := k) (F := F)
      (FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega + placeDivisor P)), ?_⟩
    exact (globalAdeleSimplePoleResidueSum
      (k := k) (F := F) omega homega).map_zero
  · letI : Algebra k P.residueField := residueAlgebra P
    letI : FiniteDimensional k P.residueField :=
      residueField_finiteDimensional P
    obtain ⟨z, hz⟩ := (Algebra.trace_surjective k P.residueField) c
    obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective z
    let eta : Differential.simplePoleDifferentialLattice P :=
      r • Differential.uniformizerLogDifferential (k := k) (F := F) P
    have hetaResidue :
        Differential.simplePoleResidue (k := k) (F := F) P eta = z := by
      change Differential.simplePoleResidue (k := k) (F := F) P
        (r • Differential.uniformizerLogDifferential (k := k) (F := F) P) = z
      rw [Differential.simplePoleResidue_smul,
        Differential.simplePoleResidue_uniformizerLogDifferential, mul_one]
      change IsLocalRing.residue P.valuationRing r = z
      exact hr
    have hetaTrace :
        Differential.simplePoleTraceResidue (k := k) (F := F) P
          (eta : Differential k F) eta.property = c := by
      change Algebra.trace k P.residueField
        (Differential.simplePoleResidue (k := k) (F := F) P eta) = c
      rw [hetaResidue, hz]
    have hetaNe : (eta : Differential k F) ≠ 0 := by
      intro hetaZero
      have htraceZero := simplePoleTraceResidue_congr
        (k := k) (F := F) P eta.property
          (Differential.simplePoleDifferentialLattice P).zero_mem hetaZero
      rw [hetaTrace,
        Differential.simplePoleTraceResidue_zero (k := k) (F := F) P] at htraceZero
      exact hc htraceZero
    let C : Differential k F →ₗ[F] F :=
      FunctionFieldDifferential.functionFieldDifferentialCoordinate
        (k := k) (F := F)
    have hComega : C omega ≠ 0 :=
      (FunctionFieldDifferential.functionFieldDifferentialCoordinate_ne_zero_iff
        (k := k) (F := F) omega).mpr homega
    have hCeta : C (eta : Differential k F) ≠ 0 :=
      (FunctionFieldDifferential.functionFieldDifferentialCoordinate_ne_zero_iff
        (k := k) (F := F) (eta : Differential k F)).mpr hetaNe
    let f : F := C (eta : Differential k F) / C omega
    have hf : f ≠ 0 := div_ne_zero hCeta hComega
    have hfomega : f • omega = (eta : Differential k F) := by
      apply (FunctionFieldDifferential.functionFieldDifferentialEquiv
        (k := k) (F := F)).injective
      change C (f • omega) = C (eta : Differential k F)
      rw [map_smul]
      change (C (eta : Differential k F) / C omega) * C omega =
        C (eta : Differential k F)
      exact div_mul_cancel₀ _ hComega
    have hfSimple : f • omega ∈
        Differential.simplePoleDifferentialLattice P := by
      rw [hfomega]
      exact eta.property
    have horder :=
      (Differential.smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
        (k := k) (F := F) P f hf omega homega).mp hfSimple
    let a₀ : GlobalAdele (k := k) (F := F) :=
      globalAdeleUpdate (k := k) (F := F)
        (zeroGlobalAdele (k := k) (F := F)) P f
    have ha₀ : a₀ ∈ globalAdeleFilter (k := k) (F := F)
        (K + placeDivisor P) := by
      intro Q
      by_cases hQP : Q = P
      · subst Q
        have hlog : WithZero.log (P.valuation f) ≤
            FunctionFieldDifferential.differentialOrder
              (k := k) (F := F) P omega homega + 1 := by
          change -1 ≤ -WithZero.log (P.valuation f) +
            FunctionFieldDifferential.differentialOrder
              (k := k) (F := F) P omega homega at horder
          omega
        have hvaluation : P.valuation f ≤ WithZero.exp
            (FunctionFieldDifferential.differentialOrder
              (k := k) (F := F) P omega homega + 1) :=
          (WithZero.log_le_iff_le_exp ((P.valuation).ne_zero_iff.mpr hf)).mp hlog
        simpa only [a₀, globalAdeleUpdate, Function.update_self, K,
          Finsupp.add_apply,
          FunctionFieldDifferential.differentialDivisor_apply,
          placeDivisor_apply] using hvaluation
      · have hzero : a₀.val Q = 0 := by
          simp only [a₀, globalAdeleUpdate, zeroGlobalAdele,
            Function.update_of_ne hQP, Pi.zero_apply]
        rw [hzero, map_zero]
        exact zero_le
    refine ⟨⟨a₀, ha₀⟩, ?_⟩
    let aSimple : globalAdeleSimplePoleSubmodule (k := k) (F := F) omega :=
      ⟨a₀,
        globalAdeleFilter_add_placeDivisor_le_globalAdeleSimplePoleSubmodule
          (k := k) (F := F) omega homega P ha₀⟩
    have hfamily : globalAdeleSimplePoleResidue
        (k := k) (F := F) omega homega aSimple = Finsupp.single P c := by
      ext Q
      by_cases hQP : Q = P
      · subst Q
        change Differential.simplePoleTraceResidue (k := k) (F := F) P
            (a₀.val P • omega) (aSimple.property P) =
          (Finsupp.single P c) P
        have haP : a₀.val P = f := by
          simp only [a₀, globalAdeleUpdate, Function.update_self]
        calc
          _ = Differential.simplePoleTraceResidue (k := k) (F := F) P
              (eta : Differential k F) eta.property := by
            apply simplePoleTraceResidue_congr (k := k) (F := F) P
            rw [haP]
            exact hfomega
          _ = c := hetaTrace
          _ = (Finsupp.single P c) P := by simp
      · change Differential.simplePoleTraceResidue (k := k) (F := F) Q
            (a₀.val Q • omega) (aSimple.property Q) =
          (Finsupp.single P c) Q
        have haQ : a₀.val Q = 0 := by
          simp only [a₀, globalAdeleUpdate, zeroGlobalAdele,
            Function.update_of_ne hQP, Pi.zero_apply]
        calc
          _ = Differential.simplePoleTraceResidue (k := k) (F := F) Q 0
              (Differential.simplePoleDifferentialLattice Q).zero_mem := by
            apply simplePoleTraceResidue_congr (k := k) (F := F) Q
            rw [haQ, zero_smul]
          _ = 0 := Differential.simplePoleTraceResidue_zero
            (k := k) (F := F) Q
          _ = (Finsupp.single P c) Q := by simp [hQP]
    change (globalAdeleSimplePoleResidue
      (k := k) (F := F) omega homega aSimple).sum
        (fun _ residue => residue) = c
    rw [hfamily]
    exact Finsupp.sum_single_index rfl
end QEC.Coding.AlgebraicGeometry.GlobalPlace
