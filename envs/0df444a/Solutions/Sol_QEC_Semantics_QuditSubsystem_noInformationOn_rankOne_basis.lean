-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.noInformationOn_rankOne_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:30:37.429437+00:00
-- url     : https://prove2.me/submissions/fa874deb-f501-4788-bcbe-038fd291d152

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_validEffect_rankOne_basis_diagonal
import Theorems.Thm_QEC_Semantics_validEffect_half_rankOne_add
import Theorems.Thm_QEC_Semantics_validEffect_half_rankOne_add_I_smul
import Theorems.Thm_QEC_Semantics_rankOne_basis_polarization
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_smul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_smul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_add
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
    {C : QuantumCode (Qudit.QuditRegister q)} {S : QuditSubsystem q}
    (hInformation : NoInformationOn C S)
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex S.selectedSystem)
    (i j : κ) :
    ScalarCompression C
      (S.extendLocalToRegister (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap) := by
  by_cases hij : i = j
  · subst j
    exact hInformation _ (validEffect_rankOne_basis_diagonal b i)
  · have hPlus : ScalarCompression C
        (S.extendLocalToRegister ((2 : Complex)⁻¹ •
          (InnerProductSpace.rankOne Complex (b i + b j) (b i + b j)).toLinearMap)) :=
        hInformation _ (validEffect_half_rankOne_add b hij)
    have hPhase : ScalarCompression C
        (S.extendLocalToRegister ((2 : Complex)⁻¹ •
          (InnerProductSpace.rankOne Complex (b i + Complex.I • b j)
            (b i + Complex.I • b j)).toLinearMap)) :=
        hInformation _ (validEffect_half_rankOne_add_I_smul b hij)
    have hDiagonalI : ScalarCompression C
        (S.extendLocalToRegister (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap) :=
      hInformation _ (validEffect_rankOne_basis_diagonal b i)
    have hDiagonalJ : ScalarCompression C
        (S.extendLocalToRegister (InnerProductSpace.rankOne Complex (b j) (b j)).toLinearMap) :=
      hInformation _ (validEffect_rankOne_basis_diagonal b j)
    have hPlus' : ScalarCompression C ((2 : Complex)⁻¹ •
        S.extendLocalToRegister
          (InnerProductSpace.rankOne Complex (b i + b j) (b i + b j)).toLinearMap) := by
      simpa only [S.extendLocalToRegister_smul] using hPlus
    have hPhase' : ScalarCompression C ((2 : Complex)⁻¹ •
        S.extendLocalToRegister
          (InnerProductSpace.rankOne Complex (b i + Complex.I • b j)
            (b i + Complex.I • b j)).toLinearMap) := by
      simpa only [S.extendLocalToRegister_smul] using hPhase
    have hPolarized := (hPlus'.add (hPhase'.smul Complex.I)).add
      ((hDiagonalI.add hDiagonalJ).smul (-(1 + Complex.I) * (2 : Complex)⁻¹))
    rw [rankOne_basis_polarization]
    rw [sub_eq_add_neg]
    rw [S.extendLocalToRegister_add, S.extendLocalToRegister_add]
    rw [S.extendLocalToRegister_smul, S.extendLocalToRegister_smul]
    rw [show -(((1 + Complex.I) * (2 : Complex)⁻¹) •
        ((InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap +
          (InnerProductSpace.rankOne Complex (b j) (b j)).toLinearMap)) =
        (-(1 + Complex.I) * (2 : Complex)⁻¹) •
          ((InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap +
            (InnerProductSpace.rankOne Complex (b j) (b j)).toLinearMap) by module]
    have hDiagonalSum :
        S.extendLocalToRegister
          ((-(1 + Complex.I) * (2 : Complex)⁻¹) •
            ((InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap +
              (InnerProductSpace.rankOne Complex (b j) (b j)).toLinearMap)) =
          (-(1 + Complex.I) * (2 : Complex)⁻¹) •
            (S.extendLocalToRegister (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap +
              S.extendLocalToRegister (InnerProductSpace.rankOne Complex (b j) (b j)).toLinearMap) := by
      rw [S.extendLocalToRegister_smul]
      rw [S.extendLocalToRegister_add]
    have hPhaseTerm :
        S.extendLocalToRegister ((2 : Complex)⁻¹ •
          (InnerProductSpace.rankOne Complex (b i + Complex.I • b j)
            (b i + Complex.I • b j)).toLinearMap) =
          (2 : Complex)⁻¹ • S.extendLocalToRegister
            (InnerProductSpace.rankOne Complex (b i + Complex.I • b j)
              (b i + Complex.I • b j)).toLinearMap :=
      S.extendLocalToRegister_smul _ _
    rw [hPhaseTerm, hDiagonalSum]
    exact hPolarized
end QEC.Semantics.QuditSubsystem
