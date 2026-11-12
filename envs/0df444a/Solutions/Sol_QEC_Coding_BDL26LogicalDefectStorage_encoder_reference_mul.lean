-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.encoder_reference_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:26:41.616944+00:00
-- url     : https://prove2.me/submissions/77b27af5-861e-4d84-a846-11a6e1888c2d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_gibbs_eq_thermal_reference
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_thermalEncoding_eq_mul_encodedObservable


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
    encoder S n beta eta.toOperator = (reference S n beta).toOperator * observable S n eta := by
  rw [show reference S n beta = (logical S n).thermalReferenceState
    (BDL26PairedDecoderGibbs.auxiliaryGibbs S n beta) from BDL26PairedDecoderGibbs.gibbs_eq_thermal_reference S n beta]
  exact (logical S n).thermalEncoding_eq_mul_encodedObservable _ eta
end QEC.Coding.BDL26LogicalDefectStorage
