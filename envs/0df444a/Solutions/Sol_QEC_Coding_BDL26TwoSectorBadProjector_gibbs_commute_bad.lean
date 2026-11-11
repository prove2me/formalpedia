-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.gibbs_commute_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:21:10.819877+00:00
-- url     : https://prove2.me/submissions/3c79f587-523d-4ccd-becb-d3f1dda90d86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_gibbs_commute

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TwoSectorBadProjector
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_24
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_25
namespace QEC.Coding.BDL26TwoSectorBadProjector
theorem _root_.solution (β : ℝ) (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    Commute (gibbs S n β).toOperator (1 - Pjoint S n BX BZ) :=
  (Commute.one_right _).sub_right (gibbs_commute S n β (goodJoint S n BX BZ))
end QEC.Coding.BDL26TwoSectorBadProjector
