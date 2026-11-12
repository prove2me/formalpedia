-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.frequency_protection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:11:45.319001+00:00
-- url     : https://prove2.me/submissions/1f6a08b5-5a39-4479-9f86-03378f2a5713

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_actual_frequency_X
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_actual_frequency_Z
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
theorem _root_.solution (q : Physical S (n+2)) (axis : CSSDaviesLocality.Axis) (omega : ℝ) :
    (Davies.actualFrequency (hamiltonian S (n+2))
      (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
      (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega * (logical S n).x -
      (logical S n).x * Davies.actualFrequency (hamiltonian S (n+2))
      (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
      (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega) * projector S n = 0 ∧
    (Davies.actualFrequency (hamiltonian S (n+2))
      (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
      (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega * (logical S n).z -
      (logical S n).z * Davies.actualFrequency (hamiltonian S (n+2))
      (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
      (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega) * projector S n = 0 :=
  ⟨BDL26LogicalDefectProtection.actual_frequency_X S n q axis omega,
    BDL26LogicalDefectProtection.actual_frequency_Z S n q axis omega⟩
end QEC.Coding.BDL26LogicalDefectStorage
