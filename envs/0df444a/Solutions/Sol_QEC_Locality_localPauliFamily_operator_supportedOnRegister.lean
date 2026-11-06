-- Prove2me | solution 1 for QEC.Locality.localPauliFamily_operator_supportedOnRegister
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:12:34.76314+00:00
-- url     : https://prove2.me/submissions/19326aca-2757-45c6-904d-b349e2f4baab

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_extendLocal_smul

set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) :
    S.OperatorSupportedOnRegister ((localPauliFamily S).operator p) := by
  refine ⟨localPauliAmplitude S • PauliSymplectic.toQubitOperator (wordBinaryPauli S p), ?_⟩
  rw [FiniteSubsystem.extendLocalToRegister, extendLocal_smul]
  rfl
end QEC.Locality
