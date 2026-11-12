-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.logical_relations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:06:13.229206+00:00
-- url     : https://prove2.me/submissions/4c39387c-2efd-4f66-8d4e-e910da1ec2e1

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
theorem _root_.solution :
    (logical S n).x.IsSymmetric ∧ (logical S n).z.IsSymmetric ∧
    (logical S n).x * (logical S n).x = 1 ∧ (logical S n).z * (logical S n).z = 1 ∧
    (logical S n).x * (logical S n).z = -((logical S n).z * (logical S n).x) :=
  ⟨(logical S n).x_symmetric, (logical S n).z_symmetric,
    (logical S n).x_sq, (logical S n).z_sq, (logical S n).anticommute⟩
end QEC.Coding.BDL26LogicalDefectStorage
