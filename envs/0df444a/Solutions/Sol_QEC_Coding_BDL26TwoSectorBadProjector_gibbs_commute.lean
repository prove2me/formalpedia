-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.gibbs_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:24:29.96563+00:00
-- url     : https://prove2.me/submissions/78bce3a7-9d7b-4e54-ab27-ca738422b07f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_CSSGibbs_gibbs_commute_selected


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TwoSectorBadProjector
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_24
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_25
namespace QEC.Coding.BDL26TwoSectorBadProjector
theorem _root_.solution (β : ℝ) (A : Finset (JointImage S n)) :
    Commute (gibbs S n β).toOperator (selected S n A) :=
  CSSGibbs.gibbs_commute_selected _ _ (row_orthogonal S n) β A
end QEC.Coding.BDL26TwoSectorBadProjector
