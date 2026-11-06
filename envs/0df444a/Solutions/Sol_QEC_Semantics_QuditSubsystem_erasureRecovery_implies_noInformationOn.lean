-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureRecovery_implies_noInformationOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:22:10.208187+00:00
-- url     : https://prove2.me/submissions/5f6ec9f8-ce3d-46e1-b8a2-4fe602e8ebca

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_of_smul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_iff_allLocalScalarCompression
import Theorems.Thm_QEC_Semantics_QuditSubsystem_allLocalScalarCompression_of_rankOne_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementKraus_complete
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementKraus_adjoint_comp
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementKraus_toQuantumChannel_eq_replacementAfterErasureWith
import Theorems.Thm_QEC_Semantics_QuditSubsystem_scalarCompression_of_replacementKraus_matrixElement
import Theorems.Thm_QEC_Semantics_QuditSubsystem_densityEnsembleVectors_exists_ne_zero
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_matrixElementKnillLaflamme_iff_exists_correctingQuantumChannel
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecovery_transfers_to_replacement


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
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hRecovery : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery) :
    NoInformationOn C S := by
  let E := S.replacementKraus rho
  have hComplete : E.Complete := S.replacementKraus_complete rho
  let replacementRecovery := QuantumChannel.comp recovery S.erasureChannelFromRegister
  have hReplacement : Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
      (S.replacementAfterErasureWith rho) replacementRecovery :=
    S.erasureRecovery_transfers_to_replacement rho C recovery hRecovery
  have hKrausRecovery :
      ∃ replacementRecovery : QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q),
        ∀ sigma : DensityOperator (Qudit.QuditRegister q),
          DensityOperator.SupportedOn C sigma →
            replacementRecovery (E.inducedMap sigma.toOperator) = sigma.toOperator := by
    refine ⟨replacementRecovery, ?_⟩
    intro sigma hSupported
    have hCorrected := hReplacement sigma hSupported
    rw [← S.replacementKraus_toQuantumChannel_eq_replacementAfterErasureWith rho hComplete]
      at hCorrected
    exact hCorrected
  have hMatrix :=
    (FiniteKrausFamily.matrixElementKnillLaflamme_iff_exists_correctingQuantumChannel
      E C hComplete).mpr hKrausRecovery
  rcases hMatrix with ⟨scalar, hMatrix⟩
  rcases S.densityEnsembleVectors_exists_ne_zero rho with ⟨i0, hi0⟩
  apply (S.noInformationOn_iff_allLocalScalarCompression C).mpr
  apply allLocalScalarCompression_of_rankOne_basis
    (C := C) (S := S) (stdOrthonormalBasis Complex S.selectedSystem)
  intro i j
  have hProduct := S.scalarCompression_of_replacementKraus_matrixElement C rho hMatrix
    (i0, i) (i0, j)
  rw [S.replacementKraus_adjoint_comp rho] at hProduct
  exact hProduct.of_smul (inner_self_ne_zero.mpr hi0)
end QEC.Semantics.QuditSubsystem
