-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectProtection.tail_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:34:32.672815+00:00
-- url     : https://prove2.me/submissions/1098ae1e-245c-44a8-8945-1599ba51ce63

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_projector_eq_joint
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_tail_union_bound


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
theorem _root_.solution (beta : ℝ) :
    clbtGibbsTailMass (protectedProjector S n) (gibbs S (n+2) beta) ≤
      BDL26TwoSectorBadProjector.pX S (n+2) beta (badX S n) +
      BDL26TwoSectorBadProjector.pZ S (n+2) beta (badZ S n) := by
  rw [projector_eq_joint]
  exact BDL26TwoSectorBadProjector.tail_union_bound S (n+2) beta _ _
end QEC.Coding.BDL26LogicalDefectProtection
