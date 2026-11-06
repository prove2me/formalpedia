-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.binaryCSSQuantumCodeOfDualLe_pairwise_toQubitOperator_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:46:37.634245+00:00
-- url     : https://prove2.me/submissions/a82bfd06-8e44-4663-9a2f-f51e07a3dc1a

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
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    ∀ P : Binary ι, P ∈ binaryCSSCheckSet xCode zCode →
      ∀ Q : Binary ι, Q ∈ binaryCSSCheckSet xCode zCode →
        toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P :=
  pairwise_toQubitOperator_commute_of_commutes
    (binaryCSSCheckSet_pairwise_commutes_of_dual_le xCode zCode hdual)
end QEC.Coding.PauliSymplectic
