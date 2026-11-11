-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectProtection.residual_single_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:42:15.637198+00:00
-- url     : https://prove2.me/submissions/88be88ad-d1ea-4f08-b173-55a6bbfa1819

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_pairedResidual_xPart
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_pairedResidual_zPart

section
noncomputable section
namespace QEC.Coding.BDL26LogicalDefectProtection
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators
variable (S : OddScale) (n : Nat)
private theorem translateX_zero (u : XSyndromeDomain S n) : translateX S n u 0 = u := by
  apply Subtype.ext
  change u.val + zSyndrome S (n+2) 0 = u.val
  rw [map_zero, add_zero]
private theorem word_add_self (a : W S n) : a + a = 0 := by
  funext q
  exact CharTwo.add_self_eq_zero (a q)
end QEC.Coding.BDL26LogicalDefectProtection
end
end

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
theorem _root_.solution (s : Visible S n) (q : Physical S (n+2)) :
    (residual S n s (CSSDaviesLocality.singlePauli q .z)).vector.xPart = 0 ∧
    (residual S n s (CSSDaviesLocality.singlePauli q .z)).vector.zPart = deltaZ S n s.2 q := by
  constructor
  · rw [BDL26PairedDecoderPhase.residual, pairedResidual_xPart]
    change xCorrection S n (translateX S n s.1 0) + 0 + xCorrection S n s.1 = 0
    rw [translateX_zero, add_zero, word_add_self]
  · exact pairedResidual_zPart S n s.1 s.2 _
end QEC.Coding.BDL26LogicalDefectProtection
