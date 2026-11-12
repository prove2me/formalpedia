-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.zero_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:12:44.728479+00:00
-- url     : https://prove2.me/submissions/3999b4b3-6c06-4003-aaa1-173820af9931

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_left_inverse
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_traceNorm_eq_zero_iff
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.finiteLindbladEvolutionLinearMap_zero



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
theorem _root_.solution (rate : Rate S n) (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace) :
    encodedError S n rate beta eta 0 (le_refl 0) = 0 ∧
    decodedError S n rate beta eta 0 (le_refl 0) = 0 := by
  constructor
  · change traceNorm (finiteLindbladEvolutionLinearMap (hamiltonian S (n+2))
      (jumps S n rate) 0 (encoder S n beta eta.toOperator) - encoder S n beta eta.toOperator) = 0
    rw [finiteLindbladEvolutionLinearMap_zero, LinearMap.id_apply, sub_self]
    exact (traceNorm_eq_zero_iff _).2 rfl
  · change traceNorm (decoder S n (finiteLindbladEvolutionLinearMap (hamiltonian S (n+2))
      (jumps S n rate) 0 (encoder S n beta eta.toOperator)) - eta.toOperator) = 0
    rw [finiteLindbladEvolutionLinearMap_zero, LinearMap.id_apply, left_inverse, sub_self]
    exact (traceNorm_eq_zero_iff _).2 rfl
end QEC.Coding.BDL26LogicalDefectStorage
