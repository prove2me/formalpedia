-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectProtection.maximal_protection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:28:51.068882+00:00
-- url     : https://prove2.me/submissions/9c9d360c-cd1a-44bb-8e51-e7d3930127f3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_selection_protected_iff
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_maximal_product_iff
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution (A : Finset (Visible S n)) :
    Protects S n A ↔ BDL26TwoSectorBadProjector.selected S (n+2) A * protectedProjector S n =
      BDL26TwoSectorBadProjector.selected S (n+2) A :=
  (selection_protected_iff S n A).trans (maximal_product_iff S n A).symm
end QEC.Coding.BDL26LogicalDefectProtection
