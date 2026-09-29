-- Prove2me | solution 1 for TarchaBraids.strandExtension_braidWord_eval_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T16:46:30.229325+00:00
-- url     : https://prove2.me/submissions/c146d690-f902-48cb-95f2-4909f878dfb0

import Mathlib
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_strand_extension_v1

open BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension

/-- Adding a far-right strand commutes with evaluating any finite signed
half-twist word, with the generator indices embedded by Fin.castLE. -/
theorem solution (n : ℕ) (w : List (BraidLetter (n + 1))) :
    (FundamentalGroup.mapOfEq (TarchaBraids.StrandExtension.addU (n + 1))
      (TarchaBraids.StrandExtension.addU_base (n + 1)))
      (FreeGroup.lift (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)
        (braidWordFree w)) =
    FreeGroup.lift (fun i : Fin (n + 2 - 1) => halfTwistBraid (n + 2) i)
      (braidWordFree (w.map (fun a =>
        ({ index := Fin.castLE (by omega) a.index, sign := a.sign } :
          BraidLetter (n + 2))))) := by
  induction w with
  | nil =>
    change (FundamentalGroup.mapOfEq (addU (n + 1)) (addU_base (n + 1))) (1) = 1
    exact map_one _
  | cons a w ih =>
    cases a with
    | mk i s =>
      cases s
      · simp only [List.map_cons, braidWordFree, braidLetterFree,
          FreeGroup.lift_apply_of, map_mul]
        rw [addU_halfTwist, ih]
      · simp only [List.map_cons, braidWordFree, braidLetterFree,
          FreeGroup.lift_apply_of, map_mul, map_inv]
        rw [addU_halfTwist, ih]
