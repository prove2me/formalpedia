-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.left_inverse_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:21:26.980003+00:00
-- url     : https://prove2.me/submissions/6310a003-11ee-449d-a614-b0f30fffb980

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_readout_encoding_density


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
    (decoder S n).mapDensity ((encoder S n beta).mapDensity eta) = eta :=
  BDL26PairedDecoderGibbs.readout_encoding_density S n beta eta
end QEC.Coding.BDL26LogicalDefectStorage
