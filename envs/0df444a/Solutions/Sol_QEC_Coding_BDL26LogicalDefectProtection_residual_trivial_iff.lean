-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectProtection.residual_trivial_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:52:02.609834+00:00
-- url     : https://prove2.me/submissions/79e1de45-aace-477c-9c73-970a56d063a4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_residual_x_boundary_iff
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_residual_z_boundary_iff
import Theorems.Thm_QEC_Coding_PauliSymplectic_inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalDefectProtection
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26LogicalDefectProtection._p2m_local_instance_6c2d909602_23
attribute [local instance] QEC.Coding.BDL26LogicalDefectProtection._p2m_local_instance_6c2d909602_24
namespace QEC.Coding.BDL26LogicalDefectProtection
theorem _root_.solution (s : Visible S n) (E : Binary (Physical S (n+2))) :
    (code S n).InGeneratedGroupUpToSign (residual S n s E) ↔
      dX S n s E = 0 ∧ dZ S n s E = 0 := by
  rw [inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff,
    mem_parityCheckRowCode, mem_parityCheckRowCode,
    residual_x_boundary_iff, residual_z_boundary_iff]
end QEC.Coding.BDL26LogicalDefectProtection
