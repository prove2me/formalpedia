-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.pairwise_toQubitOperator_commute_of_stabilizerCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:46:30.192575+00:00
-- url     : https://prove2.me/submissions/7ac23488-e9ab-40b9-bdd0-e321906639db

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_pairwise_toQubitOperator_commute_of_commutes

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
    (S : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    ∀ P : Binary ι, P ∈ S.stabilizers → ∀ Q : Binary ι, Q ∈ S.stabilizers →
      toQubitOperator P * toQubitOperator Q =
        toQubitOperator Q * toQubitOperator P :=
  pairwise_toQubitOperator_commute_of_commutes S.isotropic
end QEC.Coding.PauliSymplectic
