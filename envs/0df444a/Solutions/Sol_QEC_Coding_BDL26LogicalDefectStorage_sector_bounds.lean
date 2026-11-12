-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.sector_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:32:06.436206+00:00
-- url     : https://prove2.me/submissions/5d728956-fd08-479e-ad19-373e543c79ce

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_pX_bounds
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_pZ_bounds


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
theorem _root_.solution (beta : ℝ) :
    (0 ≤ xMass S n beta ∧ xMass S n beta ≤ 1) ∧ (0 ≤ zMass S n beta ∧ zMass S n beta ≤ 1) :=
  ⟨BDL26TwoSectorBadProjector.pX_bounds S (n+2) beta _,
    BDL26TwoSectorBadProjector.pZ_bounds S (n+2) beta _⟩
end QEC.Coding.BDL26LogicalDefectStorage
