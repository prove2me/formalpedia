-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.noInformationOn_iff_allLocalScalarCompression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:33:04.548378+00:00
-- url     : https://prove2.me/submissions/9f25f888-166f-4f74-8aae-d12ca973f3b1

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_smul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_smul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_sum
import Theorems.Thm_QEC_Semantics_QuditSubsystem_operator_eq_sum_rankOne_matrix_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_rankOne_basis

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
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q) :
    NoInformationOn C S ↔ AllLocalScalarCompression C S := by
  constructor
  · intro hInformation A
    let b := stdOrthonormalBasis Complex S.selectedSystem
    rw [operator_eq_sum_rankOne_matrix_basis b A]
    rw [S.extendLocalToRegister_sum Finset.univ]
    apply ScalarCompression.sum
    intro i
    rw [S.extendLocalToRegister_sum Finset.univ]
    apply ScalarCompression.sum
    intro j
    rw [S.extendLocalToRegister_smul]
    exact (noInformationOn_rankOne_basis hInformation b j i).smul
      (inner Complex (b j) (A (b i)))
  · intro hAll E _
    exact hAll E
end QEC.Semantics.QuditSubsystem
