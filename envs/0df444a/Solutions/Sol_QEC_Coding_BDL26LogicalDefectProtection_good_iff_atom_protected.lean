-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectProtection.good_iff_atom_protected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:11:57.442199+00:00
-- url     : https://prove2.me/submissions/6e13d42d-c9a0-4eec-ac06-f542ae5e0b4d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_residual_trivial_iff
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_protected_Z_iff
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_protected_X_iff
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_good_iff_residuals

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
theorem _root_.solution (s : Visible S n) :
    s ∈ good S n ↔ ∀ q axis,
    (BDL26CSSDaviesLocality.coupling S (n+2) q axis * BDL26PairedDecoderChannel.dressedX S n -
      BDL26PairedDecoderChannel.dressedX S n * BDL26CSSDaviesLocality.coupling S (n+2) q axis) * atom S n s = 0 ∧
    (BDL26CSSDaviesLocality.coupling S (n+2) q axis * BDL26PairedDecoderChannel.dressedZ S n -
      BDL26PairedDecoderChannel.dressedZ S n * BDL26CSSDaviesLocality.coupling S (n+2) q axis) * atom S n s = 0 := by
  rw [good_iff_residuals]
  apply forall_congr'
  intro q
  apply forall_congr'
  intro axis
  rw [residual_trivial_iff, ← protected_X_iff, ← protected_Z_iff]
  exact and_comm
end QEC.Coding.BDL26LogicalDefectProtection
