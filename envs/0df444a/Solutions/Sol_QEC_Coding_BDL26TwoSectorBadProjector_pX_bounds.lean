-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.pX_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:28:06.068661+00:00
-- url     : https://prove2.me/submissions/eaf56dfa-6405-41b2-bed8-3296993282ab

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_CSSGibbs_rowProbability_selection_bounds


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TwoSectorBadProjector
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_24
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_25
namespace QEC.Coding.BDL26TwoSectorBadProjector
theorem _root_.solution (β : ℝ) (BX : Finset (XImage S n)) :
    0 ≤ pX S n β BX ∧ pX S n β BX ≤ 1 :=
  CSSGibbs.rowProbability_selection_bounds _ (2*β) BX
end QEC.Coding.BDL26TwoSectorBadProjector
