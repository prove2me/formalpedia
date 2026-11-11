-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.projection_joint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:14:12.550662+00:00
-- url     : https://prove2.me/submissions/6427e6b7-e017-424b-9ca9-b711e374ec0e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_CSSGibbs_selectedProjector_starProjection


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TwoSectorBadProjector
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_24
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_25
namespace QEC.Coding.BDL26TwoSectorBadProjector
theorem _root_.solution (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    IsStarProjection (Pjoint S n BX BZ) :=
  CSSGibbs.selectedProjector_starProjection _ _ (row_orthogonal S n) _
end QEC.Coding.BDL26TwoSectorBadProjector
