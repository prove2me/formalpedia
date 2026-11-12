-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.even_tail_two_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:57:45.915198+00:00
-- url     : https://prove2.me/submissions/854520b8-4f19-48be-adcd-a42f340a33ea

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_tail_two_bounds

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TwoSectorBadProjector
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_24
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_25
namespace QEC.Coding.BDL26TwoSectorBadProjector
theorem _root_.solution (k : Nat) (β εX εZ : ℝ)
    (BX : Finset (XImage S (2*k))) (BZ : Finset (ZImage S (2*k)))
    (hX : pX S (2*k) β BX ≤ εX) (hZ : pZ S (2*k) β BZ ≤ εZ) :
    clbtGibbsTailMass (Pjoint S (2*k) BX BZ) (gibbs S (2*k) β) ≤ εX+εZ :=
  tail_two_bounds S (2*k) β εX εZ BX BZ hX hZ
end QEC.Coding.BDL26TwoSectorBadProjector
