-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectProtection.logical_Y_protected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:29:03.91621+00:00
-- url     : https://prove2.me/submissions/23b6dc23-172b-4daa-b708-cd219c2cb11d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_projector_dressed_Z
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_actual_XYZ_protected
import Theorems.Thm_QEC_Semantics_JumpProtected_mul_of_commute_projector
import Theorems.Thm_QEC_Semantics_JumpProtected_smul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_smul


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
theorem _root_.solution (q : Physical S (n+2)) (axis : CSSDaviesLocality.Axis) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q axis * BDL26PairedDecoderChannel.dressedY S n -
      BDL26PairedDecoderChannel.dressedY S n * BDL26CSSDaviesLocality.coupling S (n+2) q axis) *
        protectedProjector S n = 0 := by
  let J : BDL26CSSDaviesLocality.CouplingIndex S (n+2) → BDL26PairedDecoderChannel.Op S n :=
    fun qa => BDL26CSSDaviesLocality.coupling S (n+2) qa.1 qa.2
  have hx : JumpProtected J (BDL26PairedDecoderChannel.dressedX S n) (protectedProjector S n) :=
    fun qa => (actual_XYZ_protected S n qa.1 qa.2).1
  have hz : JumpProtected J (BDL26PairedDecoderChannel.dressedZ S n) (protectedProjector S n) :=
    fun qa => (actual_XYZ_protected S n qa.1 qa.2).2
  exact ((hx.mul_of_commute_projector hz (projector_dressed_Z S n)).smul Complex.I) (q,axis)
end QEC.Coding.BDL26LogicalDefectProtection
