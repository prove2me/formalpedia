-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.encoded_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:48:16.689494+00:00
-- url     : https://prove2.me/submissions/3b6d6113-9dd3-40ff-8048-08523ebbbf1d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_hamiltonian_encoder
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_generator_bound
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric
import Theorems.Thm_QEC_Semantics_QuantumChannel_map_isSymmetric
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolution_traceNorm_sub_le_time_mul


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
theorem _root_.solution (rate : Rate S n) (beta : ℝ)
    (hn : ∀ qa omega, 0 ≤ rate qa omega)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n rate beta eta t ht ≤ 8 * t * g S n rate * mass S n beta := by
  have htime := finiteLindbladEvolution_traceNorm_sub_le_time_mul
    (hamiltonian S (n+2)) (jumps S n rate)
    (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2)) (encoder S n beta eta.toOperator)
    ((encoder S n beta).map_isSymmetric eta.positive.isSymmetric)
    (hamiltonian_encoder S n beta eta) t ht
  have hlocal := mul_le_mul_of_nonneg_left (generator_bound S n rate beta hn hDB eta) ht
  calc
    encodedError S n rate beta eta t ht =
        traceNorm (finiteLindbladEvolutionLinearMap (hamiltonian S (n+2)) (jumps S n rate) t
          (encoder S n beta eta.toOperator) - encoder S n beta eta.toOperator) := rfl
    _ ≤ t * traceNorm (lindbladDissipator (jumps S n rate) (encoder S n beta eta.toOperator)) := htime
    _ ≤ t * (8 * g S n rate * mass S n beta) := hlocal
    _ = 8 * t * g S n rate * mass S n beta := by ring
end QEC.Coding.BDL26LogicalDefectStorage
