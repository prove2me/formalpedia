-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.generator_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:42:40.469196+00:00
-- url     : https://prove2.me/submissions/7806e8ec-11af-4b2f-bb13-9c7f4b9d613f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_projector_properties
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_observable_norm
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_observable_symmetric
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_observable_projector
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_observable_protected
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_encoder_mul_reference
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_observable_reference
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_projector_reference
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_stationary
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_g_eq_lindblad
import Theorems.Thm_QEC_Semantics_clbtFourBlockGeneratorEstimate


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
    (eta : DensityOperator Qubit.QubitSpace) :
    traceNorm (lindbladDissipator (jumps S n rate) (encoder S n beta eta.toOperator)) ≤
      8 * g S n rate * mass S n beta := by
  rw [encoder_mul_reference, g_eq_lindblad]
  exact clbtFourBlockGeneratorEstimate (jumps S n rate) (observable S n eta)
    (projector S n) (reference S n beta) (observable_protected S n rate eta)
    (observable_symmetric S n eta) (projector_properties S n).1
    (observable_projector S n eta) (observable_reference S n beta eta)
    (projector_reference S n beta) (stationary S n rate beta hn hDB) (observable_norm S n eta)
end QEC.Coding.BDL26LogicalDefectStorage
