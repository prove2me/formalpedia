-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedRateDavies.couplingIndex_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:46:23.715407+00:00
-- url     : https://prove2.me/submissions/b5f34e52-00df-4d5d-8794-5c690a3847e3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_axis_card

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26BoundedRateDavies
theorem _root_.solution : Fintype.card (CouplingIndex S n) =
    3 * Fintype.card (Physical S n) := by
  rw [Fintype.card_prod, axis_card, Nat.mul_comm]
end QEC.Coding.BDL26BoundedRateDavies
