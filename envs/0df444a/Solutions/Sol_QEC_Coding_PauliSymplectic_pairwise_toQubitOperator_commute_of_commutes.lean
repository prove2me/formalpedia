-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.pairwise_toQubitOperator_commute_of_commutes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:35:28.760264+00:00
-- url     : https://prove2.me/submissions/58bd2495-566a-4c51-9e2e-65e51d4d103e

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_commutes

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
    {S : Set (Binary ι)}
    (hS : ∀ P : Binary ι, P ∈ S → ∀ Q : Binary ι, Q ∈ S → Commutes P Q) :
    ∀ P : Binary ι, P ∈ S → ∀ Q : Binary ι, Q ∈ S →
      toQubitOperator P * toQubitOperator Q =
        toQubitOperator Q * toQubitOperator P := by
  intro P hP Q hQ
  exact toQubitOperator_commute_of_commutes P Q (hS P hP Q hQ)
end QEC.Coding.PauliSymplectic
