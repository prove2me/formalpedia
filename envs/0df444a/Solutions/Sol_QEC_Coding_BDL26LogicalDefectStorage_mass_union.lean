-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.mass_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:33:22.679044+00:00
-- url     : https://prove2.me/submissions/dbdc4c2b-47c1-4230-a99c-5f61fad22f4a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_tail_union_bound
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_tail_union_bound


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
theorem _root_.solution (beta : ℝ) : mass S n beta ≤ xMass S n beta + zMass S n beta :=
  BDL26LogicalDefectProtection.tail_union_bound S n beta
end QEC.Coding.BDL26LogicalDefectStorage
