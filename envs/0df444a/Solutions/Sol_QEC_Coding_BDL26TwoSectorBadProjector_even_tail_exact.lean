-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.even_tail_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:57:21.328082+00:00
-- url     : https://prove2.me/submissions/c23e2ba2-4886-4be5-845b-77792b20b85f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
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
theorem _root_.solution (k : Nat) (β : ℝ)
    (BX : Finset (XImage S (2*k))) (BZ : Finset (ZImage S (2*k))) :
    clbtGibbsTailMass (Pjoint S (2*k) BX BZ) (gibbs S (2*k) β) =
      pX S (2*k) β BX+pZ S (2*k) β BZ-pX S (2*k) β BX*pZ S (2*k) β BZ :=
  tail_exact S (2*k) β BX BZ
end QEC.Coding.BDL26TwoSectorBadProjector
