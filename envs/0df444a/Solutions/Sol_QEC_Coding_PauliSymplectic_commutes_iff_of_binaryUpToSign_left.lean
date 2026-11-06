-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.commutes_iff_of_binaryUpToSign_left
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:45:14.91797+00:00
-- url     : https://prove2.me/submissions/a47176a3-1eec-4996-9bdd-be639417f915

-- ID: 00402810-0f95-45c0-95ef-9f726d6c2758 | NAME: QEC.Coding.PauliSymplectic.commutes_iff_of_binaryUpToSign_left | 未本地编译验证
import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
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
omit [DecidableEq ι]

theorem solution {P Q R : Binary ι}
    (h : BinaryUpToSign P Q) : Commutes P R ↔ Commutes Q R := by
  have hv : P.vector = Q.vector := h
  simp [Commutes, hv]
