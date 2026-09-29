-- Prove2me | solution 1 for TarchaBraids.halfTwist_free_lift_surjective_of_normalForm_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T12:36:16.476746+00:00
-- url     : https://prove2.me/submissions/968624fc-bcc3-49fd-a2a4-fc7d853b51aa

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Theorems.Thm_TarchaBraids_braidWord_free_eval_v1

open BraidsLinksMCG TarchaBraids

/--
If every based geometric loop has a finite signed half-twist normal form, then
the free-group lift of the elementary half-twists is onto the geometric braid
group.

The only geometric input is the hypothesis `h`, namely the path-level
generation predicate from Tarcha's Theorem 3.11.  The final conversion from
the resulting word to its loop class is the already proved
`braidWord_free_eval_v1`.
-/
theorem solution
    (n : ℕ) (h : EveryLoopHasBraidWord n) :
    Function.Surjective
      (FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i)) := by
  intro g
  rcases Path.Homotopic.Quotient.mk_surjective g with ⟨f, rfl⟩
  obtain ⟨w, hw⟩ := h f
  refine ⟨braidWordFree w, ?_⟩
  change FreeGroup.lift
      (fun i : Fin (n - 1) => halfTwistBraid n i)
      (braidWordFree w) =
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk f)
  calc
    _ = FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (braidWordLoop n w)) :=
      braidWord_free_eval_v1 w
    _ = _ :=
      ((FundamentalGroupoid.fromPath_eq_iff_homotopic f (braidWordLoop n w)).2 hw).symm
