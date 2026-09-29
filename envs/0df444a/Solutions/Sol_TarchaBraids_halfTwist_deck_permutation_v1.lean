-- Prove2me | solution 1 for TarchaBraids.halfTwist_deck_permutation_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T00:28:33.038433+00:00
-- url     : https://prove2.me/submissions/a02980dd-9ede-422b-9fed-2f54af688c1c

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_endpoint_permutation_action_v1
import Theorems.Thm_TarchaBraids_configProj_isQuotientCoveringMap_v1
import Theorems.Thm_TarchaBraids_halfTwist_deck_permutation_of_quotient_v1

open BraidsLinksMCG TarchaBraids

/-- The half-twist acts on the deck-transformation fibre as the adjacent transposition,
obtained by specialising the general quotient-covering statement to the published
structure `configProj_isQuotientCoveringMap_v1`. -/
theorem solution (n : ℕ) (i : Fin (n - 1)) :
    (configProj_isQuotientCoveringMap_v1 n).fundamentalGroupToMulOpposite
      (⟨baseOrdered n, rfl⟩ : (configProj n) ⁻¹' {baseUnordered n})
      (halfTwistBraid n i) =
    MulOpposite.op (Equiv.swap (strandIdx i) (strandIdxSucc i)) :=
  halfTwist_deck_permutation_of_quotient_v1 n i (configProj_isQuotientCoveringMap_v1 n)
