-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.projection_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:54:23.495301+00:00
-- url     : https://prove2.me/submissions/003961c8-2164-4101-a29f-1e45fe383cd1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_projection_joint

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
    IsStarProjection (1 - Pjoint S n BX BZ) := (projection_joint S n BX BZ).one_sub
end QEC.Coding.BDL26TwoSectorBadProjector
