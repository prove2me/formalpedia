-- Prove2me | solution 1 for TarchaBraids.standardPureBraidWord_last_eval_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T15:56:14.457934+00:00
-- url     : https://prove2.me/submissions/087401c4-90dd-46dd-96bf-189a1e00cdf1

import Mathlib
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1

open BraidsLinksMCG TarchaBraids

/-- When the moving strand circles its immediate neighbour, the classical
word consists of exactly two copies of the final half-twist. -/
theorem solution (n : ℕ) :
    FreeGroup.lift
        (fun i : Fin (n + 2 - 1) => halfTwistBraid (n + 2) i)
        (braidWordFree (standardPureBraidWord (n + 1) (Fin.last n)))
      =
    (halfTwistBraid (n + 2) (⟨n, by omega⟩ : Fin (n + 2 - 1))) ^ 2 := by
  have hfilter :
      (List.finRange (n + 1)).filter
          (fun k : Fin (n + 1) => Fin.last n < k) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro k _
    simpa using (not_lt_of_ge (Fin.le_last k))
  -- Normalize the filter certificate to the elaborated index used by
  -- standardPureBraidWord before unfolding that definition. The earlier
  -- attempt kept Fin.last opaque in hfilter but unfolded it in the goal.
  simp only [Fin.last] at hfilter
  simp [standardPureBraidWord, Fin.last, hfilter, braidWordFree,
    braidLetterFree, pow_two]
