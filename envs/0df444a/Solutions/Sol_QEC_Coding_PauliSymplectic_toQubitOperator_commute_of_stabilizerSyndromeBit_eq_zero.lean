-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.toQubitOperator_commute_of_stabilizerSyndromeBit_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:08:48.801233+00:00
-- url     : https://prove2.me/submissions/3c9bc976-6ed0-4461-99e2-e76568aba70b

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_commutes
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerSyndromeBit_eq_zero_iff_commutes

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
    (M E : Binary ι) (h : stabilizerSyndromeBit M E = 0) :
    toQubitOperator E * toQubitOperator M = toQubitOperator M * toQubitOperator E := by
  exact toQubitOperator_commute_of_commutes E M
    ((stabilizerSyndromeBit_eq_zero_iff_commutes M E).1 h)
end QEC.Coding.PauliSymplectic
