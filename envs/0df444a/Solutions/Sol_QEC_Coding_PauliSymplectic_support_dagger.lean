-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.support_dagger
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:45:14.990902+00:00
-- url     : https://prove2.me/submissions/1f8e9e3b-bd96-4876-9401-72cb7c34a610

-- ID: a5ee5aa4-743d-4e3e-b490-aac5413cd428 | NAME: QEC.Coding.PauliSymplectic.support_dagger | 未本地编译验证
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

theorem solution (P : Binary ι) :
    support (binaryDagger P) = support P := by
  rfl
