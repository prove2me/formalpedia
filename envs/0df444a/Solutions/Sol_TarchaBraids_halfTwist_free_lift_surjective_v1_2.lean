-- Prove2me | solution 2 for TarchaBraids.halfTwist_free_lift_surjective_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T20:05:20.042709+00:00
-- url     : https://prove2.me/submissions/d69ff13b-7b8a-4c3e-a845-fe85210b826d

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Theorems.Thm_TarchaBraids_braidWord_free_eval_v1
import Theorems.Thm_TarchaBraids_every_loop_homotopic_braidWord_v1

open BraidsLinksMCG TarchaBraids

/-- Assembly candidate for `TarchaBraids.halfTwist_free_lift_surjective_v1`. -/
theorem solution (n : ℕ) :
    Function.Surjective
      (FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i)) := by
  intro g
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  obtain ⟨w, hw⟩ :=
    TarchaBraids.every_loop_homotopic_braidWord_v1 n γ
  refine ⟨braidWordFree w, ?_⟩
  rw [TarchaBraids.braidWord_free_eval_v1]
  change Path.Homotopic.Quotient.mk (braidWordLoop n w) =
    Path.Homotopic.Quotient.mk γ
  exact (Path.Homotopic.Quotient.eq).2 hw.symm
