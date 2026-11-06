-- Prove2me | solution 1 for QEC.Locality.detectableOn_embeddedLocalPauli_of_erasureCorrectableFromRegister
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:11:34.737367+00:00
-- url     : https://prove2.me/submissions/317d76a6-8508-45db-9de1-c906cb2d398a

import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Theorems.Thm_QEC_Locality_erasureCorrectableFromRegister_noInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_iff_allLocalScalarCompression
import Theorems.Thm_QEC_Semantics_QuditSubsystem_scalarCompression_iff_detectableOn


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (S : FiniteSubsystem ι) (C : QuantumCode (Qubit.QubitRegister ι))
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem C
      S.erasureChannelFromRegister recovery) (p : LocalPauliWordIndex S) :
    DetectableOn C (toQubitOperator (embeddedLocalPauli S p)) := by
  have hInformation :=
    erasureCorrectableFromRegister_noInformation S C recovery hRecovery
  have hAll :=
    ((quditSubsystemOfFinite S).noInformationOn_iff_allLocalScalarCompression C).mp
      hInformation
  have hScalar := hAll (toQubitOperator (wordBinaryPauli S p))
  apply (QuditSubsystem.scalarCompression_iff_detectableOn C _).mp
  rw [toQubitOperator_embeddedLocalPauli_eq_extendLocalToRegister]
  exact hScalar
end QEC.Locality
