-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.tail_two_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:25:01.211407+00:00
-- url     : https://prove2.me/submissions/f6953503-d06d-420a-af0c-25a44bacb8a8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_tail_union_bound
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TwoSectorBadProjector
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_24
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_25
namespace QEC.Coding.BDL26TwoSectorBadProjector
theorem _root_.solution (β εX εZ : ℝ) (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n))
    (hX : pX S n β BX ≤ εX) (hZ : pZ S n β BZ ≤ εZ) :
    clbtGibbsTailMass (Pjoint S n BX BZ) (gibbs S n β) ≤ εX+εZ :=
  (tail_union_bound S n β BX BZ).trans (add_le_add hX hZ)
end QEC.Coding.BDL26TwoSectorBadProjector
