-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.noInformationOn_implies_replacementAfterErasureWith_recovery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:53:40.621205+00:00
-- url     : https://prove2.me/submissions/ec8c7670-571d-478b-84c2-8affac9911be

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_iff_allLocalScalarCompression
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementKraus_complete
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementKraus_toQuantumChannel_eq_replacementAfterErasureWith
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementKraus_matrixElementKL_of_allLocalScalarCompression
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_matrixElementKnillLaflamme_iff_exists_correctingQuantumChannel


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
    (hInformation : NoInformationOn C S) :
    ∃ recovery : QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
        (S.replacementAfterErasureWith rho) recovery := by
  let E := S.replacementKraus rho
  have hComplete : E.Complete := S.replacementKraus_complete rho
  have hKL := S.replacementKraus_matrixElementKL_of_allLocalScalarCompression C rho
    ((S.noInformationOn_iff_allLocalScalarCompression C).mp hInformation)
  rcases (FiniteKrausFamily.matrixElementKnillLaflamme_iff_exists_correctingQuantumChannel
    E C hComplete).mp hKL with ⟨recovery, hRecovery⟩
  refine ⟨recovery, ?_⟩
  intro sigma hSupported
  rw [← S.replacementKraus_toQuantumChannel_eq_replacementAfterErasureWith rho hComplete]
  exact hRecovery sigma hSupported
end QEC.Semantics.QuditSubsystem
