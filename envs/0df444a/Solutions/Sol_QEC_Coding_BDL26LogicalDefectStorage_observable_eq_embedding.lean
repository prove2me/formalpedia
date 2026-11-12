-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.observable_eq_embedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:08:38.8324+00:00
-- url     : https://prove2.me/submissions/4e821b4f-1a70-4961-b509-5bc2b00a41b6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage

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
theorem _root_.solution (eta : DensityOperator Qubit.QubitSpace) :
    observable S n eta = (2 : ℂ) • pairEmbedding (logical S n) eta.toOperator := by
  change pairEmbedding (logical S n) ((2 : ℂ) • eta.toOperator) = _
  exact map_smul (pairEmbedding (logical S n)) (2 : ℂ) eta.toOperator
end QEC.Coding.BDL26LogicalDefectStorage
