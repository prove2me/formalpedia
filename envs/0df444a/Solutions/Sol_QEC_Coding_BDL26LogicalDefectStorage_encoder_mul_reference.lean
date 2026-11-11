-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.encoder_mul_reference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:24:48.425829+00:00
-- url     : https://prove2.me/submissions/32262c82-cfe1-4b53-ab87-172885ffec14

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_gibbs_eq_thermal_reference
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_thermalEncoding_eq_encodedObservable_mul


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
    encoder S n beta eta.toOperator = observable S n eta * (reference S n beta).toOperator := by
  rw [show reference S n beta = (logical S n).thermalReferenceState
    (BDL26PairedDecoderGibbs.auxiliaryGibbs S n beta) from BDL26PairedDecoderGibbs.gibbs_eq_thermal_reference S n beta]
  exact (logical S n).thermalEncoding_eq_encodedObservable_mul _ eta
end QEC.Coding.BDL26LogicalDefectStorage
