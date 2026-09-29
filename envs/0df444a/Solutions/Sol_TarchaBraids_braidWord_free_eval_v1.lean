-- Prove2me | solution 1 for TarchaBraids.braidWord_free_eval_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T20:02:03.90299+00:00
-- url     : https://prove2.me/submissions/a08172c0-813a-4d79-9713-1078cdc5eb32

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1

open BraidsLinksMCG TarchaBraids

/--
The free-group evaluation of a signed braid word is the fundamental-group class
of the corresponding concatenated half-twist loop.

This proof is designed around the pinned convention
`p * q = q.trans p`.
-/
theorem solution :
    ∀ {n : ℕ} (w : List (BraidLetter n)),
      FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i) (braidWordFree w) =
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (braidWordLoop n w)) := by
  intro n w
  induction w with
  | nil =>
      rw [braidWordFree, map_one, braidWordLoop, Path.Homotopic.Quotient.mk_refl]
      exact FundamentalGroup.one_def
  | cons a w ih =>
      have hletter :
          FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i) (braidLetterFree a) =
            FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk (braidLetterLoop n a)) := by
        rcases a with ⟨i, sign⟩
        cases sign <;>
          simp [braidLetterFree, braidLetterLoop, halfTwistBraid, FundamentalGroup.inv_def]
      rw [braidWordFree, map_mul, hletter, ih, FundamentalGroup.mul_def]
      rfl
