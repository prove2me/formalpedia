-- Prove2me | solution 1 for TarchaBraids.standardPureBraidWord_eval_transport_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T22:50:37.645497+00:00
-- url     : https://prove2.me/submissions/20beb012-41fa-4858-a245-21ff66f7b2c9

import Mathlib
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1
import Definitions.Def_TarchaBraids_strand_extension_v1
import Theorems.Thm_TarchaBraids_standardPureBraidWord_list_transport_v1
import Theorems.Thm_TarchaBraids_strandExtension_braidWord_eval_v2

open BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension

/-- Algebraic strand transport: classical pure-braid evaluation satisfies
the same final-generator conjugation recurrence as its signed letter list. -/
theorem solution (n : ℕ) (j : Fin n) :
    FreeGroup.lift
        (fun i : Fin (n + 2 - 1) => halfTwistBraid (n + 2) i)
        (braidWordFree (standardPureBraidWord (n + 1) j.castSucc))
      =
    halfTwistBraid (n + 2) (Fin.last n) *
      (FundamentalGroup.mapOfEq (TarchaBraids.StrandExtension.addU (n + 1))
        (TarchaBraids.StrandExtension.addU_base (n + 1)))
        (FreeGroup.lift
          (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)
          (braidWordFree (standardPureBraidWord n j))) *
      (halfTwistBraid (n + 2) (Fin.last n))⁻¹ := by
  have happ {m : ℕ} (u v : List (BraidLetter m)) :
      braidWordFree (u ++ v) = braidWordFree u * braidWordFree v := by
    induction u with
    | nil => simp [braidWordFree]
    | cons a u ih =>
      simp only [List.cons_append, braidWordFree]
      rw [ih]
      group
  calc
    FreeGroup.lift
        (fun i : Fin (n + 2 - 1) => halfTwistBraid (n + 2) i)
        (braidWordFree (standardPureBraidWord (n + 1) j.castSucc))
        =
        halfTwistBraid (n + 2) (Fin.last n) *
          (FreeGroup.lift
            (fun i : Fin (n + 2 - 1) => halfTwistBraid (n + 2) i)
            (braidWordFree ((standardPureBraidWord n j).map
              (fun a => ({ index := Fin.castLE (by omega) a.index, sign := a.sign } :
                BraidLetter (n + 2)))))) *
          (halfTwistBraid (n + 2) (Fin.last n))⁻¹ := by
      rw [standardPureBraidWord_list_transport_v1]
      simp [happ, braidWordFree, braidLetterFree, map_mul, map_inv,
        FreeGroup.lift_apply_of, mul_assoc]
    _ = _ := by
      rw [strandExtension_braidWord_eval_v2]
