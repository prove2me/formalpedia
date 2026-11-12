-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.hamiltonian_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:23:17.289717+00:00
-- url     : https://prove2.me/submissions/2040e337-5af7-46ca-922c-86d32960b766

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logicalZ_normalizer
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
theorem _root_.solution : Commute (hamiltonian S (n+2)) (logical S n).z :=
  (dressed_commute_hamiltonian S n _ (BDL26BareLogicalPair.logicalZ_normalizer S (n+2))).symm
end QEC.Coding.BDL26LogicalDefectStorage
