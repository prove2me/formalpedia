-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.tail_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:33:37.802911+00:00
-- url     : https://prove2.me/submissions/7c8c7139-9de2-4172-afb3-e213ef99ee18

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_gibbs_commute_bad
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_trace_bad

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
    clbtGibbsTailMass (Pjoint S n BX BZ) (gibbs S n β) =
      pX S n β BX+pZ S n β BZ-pX S n β BX*pZ S n β BZ := by
  unfold clbtGibbsTailMass
  rw [← (gibbs_commute_bad S n β BX BZ).eq, trace_bad, Complex.ofReal_re]
end QEC.Coding.BDL26TwoSectorBadProjector
