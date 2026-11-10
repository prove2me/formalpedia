-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.hamiltonian_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:24:01.149475+00:00
-- url     : https://prove2.me/submissions/da5c496e-9245-4912-81f3-e382289c7111

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_commute_selected


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TwoSectorBadProjector
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_24
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_25
namespace QEC.Coding.BDL26TwoSectorBadProjector
theorem _root_.solution (A : Finset (JointImage S n)) :
    Commute (hamiltonian S n) (selected S n A) :=
  CSSGibbs.hamiltonian_commute_selected _ _ (row_orthogonal S n) A
end QEC.Coding.BDL26TwoSectorBadProjector
