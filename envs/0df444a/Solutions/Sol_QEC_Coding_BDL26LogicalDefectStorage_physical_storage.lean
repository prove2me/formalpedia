-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.physical_storage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:12:54.37128+00:00
-- url     : https://prove2.me/submissions/bfab17b8-107f-463c-9333-237ecf5292e7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_storage_eight
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_storage_forty_eight

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
theorem _root_.solution (rate : Rate S n) (beta hmax : ℝ) (_hb : 0 < beta) (hm : 0 < hmax)
    (hr : ∀ qa omega, 0 < rate qa omega ∧ rate qa omega ≤ hmax)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    (encodedError S n rate beta eta t ht ≤ 8 * t * g S n rate * mass S n beta ∧
     decodedError S n rate beta eta t ht ≤ 8 * t * g S n rate * mass S n beta) ∧
    (encodedError S n rate beta eta t ht ≤ 48 * t * qubits S n * hmax * mass S n beta ∧
     decodedError S n rate beta eta t ht ≤ 48 * t * qubits S n * hmax * mass S n beta) :=
  ⟨storage_eight S n rate beta (fun qa w => (hr qa w).1.le) hDB eta t ht,
    storage_forty_eight S n rate beta hmax hm.le (fun qa w => (hr qa w).1.le)
      (fun qa w => (hr qa w).2) hDB eta t ht⟩
end QEC.Coding.BDL26LogicalDefectStorage
