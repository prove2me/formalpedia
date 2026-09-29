-- Prove2me | solution 1 for TarchaBraids.strandExtension_braidWord_eval_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T00:29:13.368423+00:00
-- url     : https://prove2.me/submissions/2e48dd89-9ff1-4d51-8ddc-086fefdccc4b

import Mathlib
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_strand_extension_v1
import Theorems.Thm_TarchaBraids_strandExtension_braidWord_eval_v2

open BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension

/-- Evaluating a braid word after adding a free strand agrees with transporting the
lower-strand evaluation along `addU`, then re-evaluating the cast word in the larger
braid group. This is the published `strandExtension_braidWord_eval_v2` restated with
the `open TarchaBraids.StrandExtension` spellings of this catalogue entry. -/
theorem solution (n : ℕ) (w : List (BraidLetter (n + 1))) :
    (FundamentalGroup.mapOfEq (addU (n + 1)) (addU_base (n + 1)))
      (FreeGroup.lift (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)
        (braidWordFree w)) =
    FreeGroup.lift (fun i : Fin (n + 2 - 1) => halfTwistBraid (n + 2) i)
      (braidWordFree (w.map (fun a =>
        ({ index := Fin.castLE (by omega) a.index, sign := a.sign } :
          BraidLetter (n + 2))))) :=
  strandExtension_braidWord_eval_v2 n w
