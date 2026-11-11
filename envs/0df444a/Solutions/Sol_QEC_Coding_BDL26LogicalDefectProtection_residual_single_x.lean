-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectProtection.residual_single_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:23:34.164953+00:00
-- url     : https://prove2.me/submissions/1ce10ec1-0f42-46e8-9814-791147e8be9d

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
private theorem translateZ_zero (v : ZSyndromeDomain S n) : translateZ S n v 0 = v := by
  apply Subtype.ext
  change v.val + xSyndrome S (n+2) 0 = v.val
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
    (residual S n s (CSSDaviesLocality.singlePauli q .x)).vector.xPart = deltaX S n s.1 q ∧
    (residual S n s (CSSDaviesLocality.singlePauli q .x)).vector.zPart = 0 := by
  constructor
  · exact pairedResidual_xPart S n s.1 s.2 _
  · rw [BDL26PairedDecoderPhase.residual, pairedResidual_zPart]
    change zCorrection S n (translateZ S n s.2 0) + 0 + zCorrection S n s.2 = 0
    rw [translateZ_zero, add_zero, word_add_self]
end QEC.Coding.BDL26LogicalDefectProtection
