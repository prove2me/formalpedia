-- Prove2me | solution 1 for QEC.Locality.erasureCorrectableFromRegister_noInformation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:09:11.737005+00:00
-- url     : https://prove2.me/submissions/7e2afc58-0d90-476f-899a-b2b2c597464a

import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecovery_implies_noInformationOn


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
      S.erasureChannelFromRegister recovery) :
    (quditSubsystemOfFinite S).NoInformationOn C := by
  exact (quditSubsystemOfFinite S).erasureRecovery_implies_noInformationOn C
    ((quditSubsystemOfFinite S).maximallyMixedSelected (by
      intro i
      norm_num)) recovery hRecovery
end QEC.Locality
