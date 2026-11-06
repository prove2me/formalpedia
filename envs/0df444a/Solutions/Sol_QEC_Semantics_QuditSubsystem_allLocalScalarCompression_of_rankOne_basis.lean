-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.allLocalScalarCompression_of_rankOne_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:25:30.597915+00:00
-- url     : https://prove2.me/submissions/bc6d2a3c-23fa-427a-98ae-e09001bfdcba

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
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex S.selectedSystem)
    (hRankOne : ∀ i j : κ,
      ScalarCompression C
        (S.extendLocalToRegister (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap)) :
    AllLocalScalarCompression C S := by
  intro A
  rw [operator_eq_sum_rankOne_matrix_basis b A]
  rw [S.extendLocalToRegister_sum Finset.univ]
  apply ScalarCompression.sum
  intro i
  rw [S.extendLocalToRegister_sum Finset.univ]
  apply ScalarCompression.sum
  intro j
  rw [S.extendLocalToRegister_smul]
  exact (hRankOne j i).smul (inner Complex (b j) (A (b i)))
end QEC.Semantics.QuditSubsystem
