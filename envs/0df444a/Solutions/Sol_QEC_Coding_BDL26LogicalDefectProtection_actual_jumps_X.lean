-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectProtection.actual_jumps_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:42:55.941915+00:00
-- url     : https://prove2.me/submissions/7de68fcd-d2af-4b87-b53d-9796d8187f18

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_projector_hamiltonian
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_actual_XYZ_protected
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_dressed_commute_hamiltonian
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Semantics_Davies_hamiltonianJump_protected


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
theorem _root_.solution
    (rate : BDL26CSSDaviesLocality.CouplingIndex S (n+2) → BDL26CSSDaviesLocality.Frequency S (n+2) → ℝ) :
    JumpProtected (BDL26BoundedRateDavies.jump S (n+2) rate)
      (BDL26PairedDecoderChannel.dressedX S n) (protectedProjector S n) := by
  apply Davies.hamiltonianJump_protected
  · exact (dressed_commute_hamiltonian S n _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2))).symm
  · exact projector_hamiltonian S n
  · intro qa
    exact (actual_XYZ_protected S n qa.1 qa.2).1
end QEC.Coding.BDL26LogicalDefectProtection
