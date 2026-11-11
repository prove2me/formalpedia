-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.projector_properties
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:09:37.100475+00:00
-- url     : https://prove2.me/submissions/7f54ca03-c091-416d-b161-cffbbf857434

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_projector_dressed_X
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_projector_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_projector_hamiltonian
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_projector_projection
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
theorem _root_.solution : IsStarProjection (projector S n) ∧
    Commute (projector S n) (hamiltonian S (n+2)) ∧
    Commute (projector S n) (logical S n).x ∧ Commute (projector S n) (logical S n).z :=
  ⟨BDL26LogicalDefectProtection.projector_projection S n,
    (BDL26LogicalDefectProtection.projector_hamiltonian S n).symm,
    (BDL26LogicalDefectProtection.projector_dressed_X S n).symm,
    (BDL26LogicalDefectProtection.projector_dressed_Z S n).symm⟩
end QEC.Coding.BDL26LogicalDefectStorage
