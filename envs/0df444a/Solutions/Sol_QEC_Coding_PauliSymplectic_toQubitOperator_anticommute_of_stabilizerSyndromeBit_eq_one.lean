-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.toQubitOperator_anticommute_of_stabilizerSyndromeBit_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:08:52.439074+00:00
-- url     : https://prove2.me/submissions/492e1216-4401-4e8d-a635-4fb2f4a1d273

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_anticommute_of_not_commutes
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerSyndromeBit_eq_one_iff_not_commutes

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
    (M E : Binary ι) (h : stabilizerSyndromeBit M E = 1) :
    toQubitOperator E * toQubitOperator M =
      -(toQubitOperator M * toQubitOperator E) := by
  exact toQubitOperator_anticommute_of_not_commutes E M
    ((stabilizerSyndromeBit_eq_one_iff_not_commutes M E).1 h)
end QEC.Coding.PauliSymplectic
