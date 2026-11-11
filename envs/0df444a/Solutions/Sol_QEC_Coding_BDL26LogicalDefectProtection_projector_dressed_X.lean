-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectProtection.projector_dressed_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:42:28.480883+00:00
-- url     : https://prove2.me/submissions/73af4d12-7b67-4029-8363-c3db3bdc7c74

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_atom_mul_phaseOperator
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_normalizer_commute_atom
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_phaseOperator_mul_atom
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
noncomputable section
namespace QEC.Coding.BDL26LogicalDefectProtection
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators
variable (S : OddScale) (n : Nat)
private theorem normalizer_selected (A : Finset (Visible S n)) (L : Binary (Physical S (n+2)))
    (hL : (code S n).InBinaryNormalizer L) :
    Commute (dressed S n L) (BDL26TwoSectorBadProjector.selected S (n+2) A) := by
  change Commute (dressed S n L) (∑ s ∈ A, atom S n s)
  apply Commute.sum_right
  intro s _
  have hc := normalizer_commute_atom S n L hL s
  have hp : Commute (phaseOperator S n L) (atom S n s) :=
    (phaseOperator_mul_atom S n L s).trans (atom_mul_phaseOperator S n L s).symm
  exact hc.mul_left hp
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
theorem _root_.solution : Commute (BDL26PairedDecoderChannel.dressedX S n) (protectedProjector S n) :=
  normalizer_selected S n _ _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2))
end QEC.Coding.BDL26LogicalDefectProtection
