-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.replacementKraus_matrixElementKL_of_allLocalScalarCompression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:34:36.01186+00:00
-- url     : https://prove2.me/submissions/f72ad556-6614-4e78-add3-aaccc40ab48a

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_scalarCompression_iff_detectableOn
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_smul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementKraus_adjoint_comp
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
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


attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator

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
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (rho : DensityOperator S.selectedSystem)
    (hLocal : AllLocalScalarCompression C S) :
    ∃ scalar :
        (Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) →
          (Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) →
            Complex,
      ∀ p r,
        ∀ x : Qudit.QuditRegister q, x ∈ C.carrier →
          ∀ y : Qudit.QuditRegister q, y ∈ C.carrier →
            inner Complex ((S.replacementKraus rho).operator p x)
              ((S.replacementKraus rho).operator r y) =
              scalar p r * inner Complex x y := by
  have hProduct (p r :
      Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) :
      ScalarCompression C
        ((LinearMap.adjoint ((S.replacementKraus rho).operator p)).comp
          ((S.replacementKraus rho).operator r)) := by
    rw [S.replacementKraus_adjoint_comp rho p r]
    exact (hLocal _).smul _
  choose scalar hScalar using fun p r =>
    (scalarCompression_iff_detectableOn C _).mp (hProduct p r)
  refine ⟨scalar, ?_⟩
  intro p r x hx y hy
  calc
    inner Complex ((S.replacementKraus rho).operator p x)
        ((S.replacementKraus rho).operator r y) =
        inner Complex x
          (((LinearMap.adjoint ((S.replacementKraus rho).operator p)).comp
            ((S.replacementKraus rho).operator r)) y) := by
              simpa [LinearMap.comp_apply] using
                (LinearMap.adjoint_inner_right (𝕜 := Complex)
                  ((S.replacementKraus rho).operator p) x
                  ((S.replacementKraus rho).operator r y)).symm
    _ = scalar p r * inner Complex x y := hScalar p r x hx y hy
end QEC.Semantics.QuditSubsystem
