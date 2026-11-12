-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.jump_coherent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:11:41.934304+00:00
-- url     : https://prove2.me/submissions/775ffcaf-d7c2-417d-8a6d-068ef9596405

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_jump_eq_sqrt_frequency
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalDefectStorage
open Classical Semantics BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26LogicalDefectStorage._p2m_local_instance_444300d501_96
attribute [local instance] QEC.Coding.BDL26LogicalDefectStorage._p2m_local_instance_444300d501_97
namespace QEC.Coding.BDL26LogicalDefectStorage
theorem _root_.solution (rate : Rate S n) (q : Physical S (n+2))
    (axis : CSSDaviesLocality.Axis) (omega : BDL26CSSDaviesLocality.Frequency S (n+2)) :
    jumps S n rate ((q,axis),omega) = (Real.sqrt (rate (q,axis) omega) : ℂ) •
      Davies.actualFrequency (hamiltonian S (n+2))
        (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
        (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega.val :=
  BDL26BoundedRateDavies.jump_eq_sqrt_frequency S (n+2) rate q axis omega
end QEC.Coding.BDL26LogicalDefectStorage
