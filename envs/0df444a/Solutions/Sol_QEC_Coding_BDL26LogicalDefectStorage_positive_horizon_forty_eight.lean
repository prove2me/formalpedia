-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.positive_horizon_forty_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:10:41.149395+00:00
-- url     : https://prove2.me/submissions/93acfebe-b1c3-4445-a6f8-df91d98ba292

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_window_forty_eight

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
theorem _root_.solution (rate : Rate S n) (beta hmax : ℝ) (hm : 0 ≤ hmax)
    (hn : ∀ qa omega, 0 ≤ rate qa omega) (hu : ∀ qa omega, rate qa omega ≤ hmax)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (hp : 0 < qubits S n * hmax * mass S n beta)
    (eta : DensityOperator Qubit.QubitSpace) (delta t : ℝ) (hd : 0 ≤ delta) (ht : 0 ≤ t)
    (hw : t ≤ delta / (48 * qubits S n * hmax * mass S n beta)) :
    encodedError S n rate beta eta t ht ≤ delta ∧ decodedError S n rate beta eta t ht ≤ delta := by
  apply window_forty_eight S n rate beta hmax hm hn hu hDB eta delta t hd ht
  have hp' : 0 < 48 * qubits S n * hmax * mass S n beta := by nlinarith
  have h := (le_div_iff₀ hp').mp hw
  nlinarith
end QEC.Coding.BDL26LogicalDefectStorage
