-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectProtection.residual_z_boundary_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:37:12.443728+00:00
-- url     : https://prove2.me/submissions/56d37ebb-1991-4d46-a7bf-c4214b6c3d47

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_z_row_iff
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_pairedResidual_closed


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
    (∃ c, wordLinearMapTranspose (zSyndrome S (n+2)) c =
      (residual S n s E).vector.zPart) ↔ dZ S n s E = 0 :=
  z_row_iff S n _ (pairedResidual_closed S n s.1 s.2 E).2
end QEC.Coding.BDL26LogicalDefectProtection
