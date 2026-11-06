-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.finitePOVMDistributionInvariant_implies_noInformationOn_of_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:29:14.577038+00:00
-- url     : https://prove2.me/submissions/ad1a5f51-dd8a-4222-a160-af0df097af44

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_scalarCompression_iff_detectableOn
import Theorems.Thm_QEC_Semantics_QuditSubsystem_trace_comp_pureOfNonzero
import Theorems.Thm_QEC_Semantics_QuditSubsystem_detectableOnWithScalar_of_quadratic_expectation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_exists_nonzero_codeword
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_supportedOn
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q)
    (hC : C.carrier ≠ ⊥) :
    FinitePOVMDistributionInvariant.{u, v} C S → NoInformationOn C S := by
  intro hDistribution E hE
  let effects : ULift.{v} Bool → Operator S.selectedSystem :=
    fun b => if b.down then E else 1 - E
  have hPOVM : FinitePOVM effects := by
    constructor
    · intro b
      rcases b with ⟨b⟩
      cases b with
      | false =>
          dsimp [effects]
          refine ⟨hE.2, ?_⟩
          convert hE.1 using 1; module
      | true => simpa [effects] using hE
    · let e : ULift.{v} Bool ≃ Bool := Equiv.ulift
      rw [Fintype.sum_equiv e effects
        (fun b : Bool => if b then E else 1 - E) (by intro b; rfl)]
      rw [Fintype.sum_bool]
      simp
  rcases exists_nonzero_codeword C hC with ⟨r, hrC, hr0⟩
  let A : Operator (Qudit.QuditRegister q) := S.extendLocalToRegister E
  let alpha : Complex := LinearMap.trace Complex (Qudit.QuditRegister q)
    (A.comp (DensityOperator.pureOfNonzero r hr0).toOperator)
  have hQuadratic : ∀ x : Qudit.QuditRegister q, x ∈ C.carrier →
      inner Complex x (A x) = alpha * inner Complex x x := by
    intro x hxC
    by_cases hx0 : x = 0
    · subst x
      simp
    · have hInvariant := hDistribution (ULift.{v} Bool) inferInstance effects hPOVM ⟨true⟩
        (DensityOperator.pureOfNonzero x hx0) (DensityOperator.pureOfNonzero r hr0)
        (DensityOperator.pureOfNonzero_supportedOn hx0 hxC)
        (DensityOperator.pureOfNonzero_supportedOn hr0 hrC)
      have hRayleigh : (inner Complex x x)⁻¹ * inner Complex x (A x) = alpha := by
        calc
          (inner Complex x x)⁻¹ * inner Complex x (A x) =
              LinearMap.trace Complex (Qudit.QuditRegister q)
                (A.comp (DensityOperator.pureOfNonzero x hx0).toOperator) := by
                  symm
                  exact trace_comp_pureOfNonzero A x hx0
          _ = LinearMap.trace Complex (Qudit.QuditRegister q)
                (A.comp (DensityOperator.pureOfNonzero r hr0).toOperator) := by
                  simpa [A, effects] using hInvariant
          _ = alpha := rfl
      rw [← hRayleigh]
      field_simp [inner_self_ne_zero.mpr hx0]
  rw [scalarCompression_iff_detectableOn]
  exact ⟨alpha, detectableOnWithScalar_of_quadratic_expectation hQuadratic⟩
end QEC.Semantics.QuditSubsystem
