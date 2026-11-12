-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.hamiltonian_commute_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:54:43.776523+00:00
-- url     : https://prove2.me/submissions/324414b8-0df3-492a-9391-aecb9e3ce48f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_hamiltonian_commute

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
    Commute (hamiltonian S n) (1 - Pjoint S n BX BZ) :=
  (Commute.one_right _).sub_right (hamiltonian_commute S n (goodJoint S n BX BZ))
end QEC.Coding.BDL26TwoSectorBadProjector
