-- Prove2me | solution 1 for PermanentRollout.blockIncidenceBase_ringKrullDim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/e650c5f5-7572-4e8c-8311-36069050540e

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_incidenceRowBlock_card

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution (b t s d : ℕ) :
    ringKrullDim
      (MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ) =
      ((b * ((2 ^ t - 1) + s * (d - 2)) : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_sum, Fintype.card_prod,
    incidenceRowBlock_card]
  simp
end PermanentRollout
