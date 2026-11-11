-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.tail_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:38:31.039404+00:00
-- url     : https://prove2.me/submissions/bfddd159-84ca-4064-a047-8d7096a0fa4d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_pX_bounds
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_pZ_bounds
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_tail_exact

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
    clbtGibbsTailMass (Pjoint S n BX BZ) (gibbs S n β) ≤ pX S n β BX+pZ S n β BZ := by
  rw [tail_exact]
  exact sub_le_self _ (mul_nonneg (pX_bounds S n β BX).1 (pZ_bounds S n β BZ).1)
end QEC.Coding.BDL26TwoSectorBadProjector
