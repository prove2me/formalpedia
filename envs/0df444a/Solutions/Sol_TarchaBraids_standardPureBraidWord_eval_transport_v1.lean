-- Prove2me | solution 1 for TarchaBraids.standardPureBraidWord_eval_transport_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T00:28:55.51576+00:00
-- url     : https://prove2.me/submissions/b86d8ab9-9027-4b4e-b2f3-e12aadda941d

import Mathlib
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1
import Definitions.Def_TarchaBraids_strand_extension_v1
import Theorems.Thm_TarchaBraids_standardPureBraidWord_list_transport_v1
import Theorems.Thm_TarchaBraids_strandExtension_braidWord_eval_v2
import Theorems.Thm_TarchaBraids_standardPureBraidWord_eval_transport_v2

open BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension

/-- Adding a strand sends the evaluation of the standard pure braid word to the
conjugate of the previous evaluation by the new elementary half-twist. This is the
published `standardPureBraidWord_eval_transport_v2` restated with the unqualified
`addU`/`addU_base` spellings of this catalogue entry. -/
theorem solution (n : ℕ) (j : Fin n) :
    FreeGroup.lift
        (fun i : Fin (n + 2 - 1) => halfTwistBraid (n + 2) i)
        (braidWordFree (standardPureBraidWord (n + 1) j.castSucc))
      =
    halfTwistBraid (n + 2) (Fin.last n) *
      (FundamentalGroup.mapOfEq (addU (n + 1)) (addU_base (n + 1)))
        (FreeGroup.lift
          (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)
          (braidWordFree (standardPureBraidWord n j))) *
      (halfTwistBraid (n + 2) (Fin.last n))⁻¹ :=
  standardPureBraidWord_eval_transport_v2 n j
