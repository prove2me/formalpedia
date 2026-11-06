-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.binaryCSSStabilizerCodeOfDualLe_pairwise_toQubitOperator_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:12:27.864108+00:00
-- url     : https://prove2.me/submissions/11dbb76e-deef-4226-90e8-332d612909c5

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_pairwise_toQubitOperator_commute_of_stabilizerCode

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
    ∀ P : Binary ι,
      P ∈ (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).stabilizers →
      ∀ Q : Binary ι,
        Q ∈ (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).stabilizers →
        toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P :=
  pairwise_toQubitOperator_commute_of_stabilizerCode
    (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual)
end QEC.Coding.PauliSymplectic
