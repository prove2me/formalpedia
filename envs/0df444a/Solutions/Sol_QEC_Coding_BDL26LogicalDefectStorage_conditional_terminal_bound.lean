-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.conditional_terminal_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:23:56.713077+00:00
-- url     : https://prove2.me/submissions/cc854c0e-b331-40f3-86dc-1a51188e0c9f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_conditional_one_ninety_two
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_peierlsScale_pos

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
    (k : Nat) (hx : xMass S n beta ≤ 2*peierlsScale k) (hz : zMass S n beta ≤ 2*peierlsScale k)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n rate beta eta t ht ≤ 192 * t * qubits S n * hmax * peierlsScale k ∧
    decodedError S n rate beta eta t ht ≤ 192 * t * qubits S n * hmax * peierlsScale k :=
  conditional_one_ninety_two S n rate beta hmax (peierlsScale k) hm (peierlsScale_pos k).le
    hn hu hDB hx hz eta t ht
end QEC.Coding.BDL26LogicalDefectStorage
