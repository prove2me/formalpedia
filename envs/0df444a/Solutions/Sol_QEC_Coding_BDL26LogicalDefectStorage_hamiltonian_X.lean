-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.hamiltonian_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:23:14.200422+00:00
-- url     : https://prove2.me/submissions/3eb0527c-2bee-4f41-9d5d-cd95c55fffb9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_dressed_commute_hamiltonian
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
theorem _root_.solution : Commute (hamiltonian S (n+2)) (logical S n).x :=
  (dressed_commute_hamiltonian S n _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2))).symm
end QEC.Coding.BDL26LogicalDefectStorage
