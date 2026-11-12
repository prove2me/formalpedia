-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.hamiltonian_encoder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:34:20.429049+00:00
-- url     : https://prove2.me/submissions/92669e18-638f-42a7-8a40-13bc14180f04

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_observable_hamiltonian
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_encoder_mul_reference
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_hamiltonian_reference
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace) :
    Commute (hamiltonian S (n+2)) (encoder S n beta eta.toOperator) := by
  rw [encoder_mul_reference]
  exact (observable_hamiltonian S n eta).symm.mul_right (hamiltonian_reference S n beta)
end QEC.Coding.BDL26LogicalDefectStorage
