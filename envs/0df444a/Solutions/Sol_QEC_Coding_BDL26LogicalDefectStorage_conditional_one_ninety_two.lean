-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.conditional_one_ninety_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:14:32.929469+00:00
-- url     : https://prove2.me/submissions/d8ac5eca-91f6-4fd3-b365-ba0b6b7344d4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_storage_forty_eight
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_sector_envelope
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
theorem _root_.solution (rate : Rate S n) (beta hmax q : ℝ) (hm : 0 ≤ hmax) (hq : 0 ≤ q)
    (hn : ∀ qa omega, 0 ≤ rate qa omega) (hu : ∀ qa omega, rate qa omega ≤ hmax)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (hx : xMass S n beta ≤ 2*q) (hz : zMass S n beta ≤ 2*q)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n rate beta eta t ht ≤ 192 * t * qubits S n * hmax * q ∧
    decodedError S n rate beta eta t ht ≤ 192 * t * qubits S n * hmax * q := by
  obtain ⟨he,hd⟩ := storage_forty_eight S n rate beta hmax hm hn hu hDB eta t ht
  have hN : 0 ≤ qubits S n := by unfold qubits; positivity
  have hc : 48 * t * qubits S n * hmax * mass S n beta ≤ 192 * t * qubits S n * hmax * q := by
    calc
      _ ≤ 48 * t * qubits S n * hmax * (4*q) :=
        mul_le_mul_of_nonneg_left (sector_envelope S n beta q hq hx hz) (by positivity)
      _ = _ := by ring
  exact ⟨he.trans hc,hd.trans hc⟩
end QEC.Coding.BDL26LogicalDefectStorage
