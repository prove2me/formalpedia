-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectProtection.residual_x_boundary_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:45:11.169906+00:00
-- url     : https://prove2.me/submissions/f5ffa52e-a874-4a64-a8df-7a14d124e293

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_x_row_iff
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
    (∃ c, wordLinearMapTranspose (xSyndrome S (n+2)) c =
      (residual S n s E).vector.xPart) ↔ dX S n s E = 0 :=
  x_row_iff S n _ (pairedResidual_closed S n s.1 s.2 E).1
end QEC.Coding.BDL26LogicalDefectProtection
