-- Prove2me | solution 2 for QEC.Coding.PauliSymplectic.binaryStabilizerCommonFixedQuantumCode_projector_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:09:46.008932+00:00
-- url     : https://prove2.me/submissions/670c1649-4f6a-4e73-813d-89ae6251c136

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_mem_carrier


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (S : Set (Binary ι)) (ψ : Semantics.Qubit.QubitRegister ι) :
    ∀ P : Binary ι, P ∈ S →
      toQubitOperator P ((binaryStabilizerCommonFixedQuantumCode S).projector ψ) =
        (binaryStabilizerCommonFixedQuantumCode S).projector ψ := by
  intro P hP
  exact
    (mem_binaryStabilizerCommonFixedQuantumCode_carrier
      (S := S) (ψ := (binaryStabilizerCommonFixedQuantumCode S).projector ψ)).1
      ((binaryStabilizerCommonFixedQuantumCode S).projector_mem_carrier ψ) P hP
end QEC.Coding.PauliSymplectic
