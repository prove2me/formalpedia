-- Prove2me | solution 1 for TarchaBraids.halfTwist_free_lift_surjective_acyclic_v1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-27T21:35:55.364839+00:00
-- url     : https://prove2.me/submissions/dcda2bde-a9f0-4fb4-97d1-771171119074
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Theorems.Thm_TarchaBraids_braidWord_free_eval_v1
import Theorems.Thm_TarchaBraids_every_loop_homotopic_braidWord_v1

open BraidsLinksMCG TarchaBraids

set_option autoImplicit false

/-- Assembly for `TarchaBraids.halfTwist_free_lift_surjective_acyclic_v1`.

Every element of the geometric braid group is the homotopy class of a based
loop (`Path.Homotopic.Quotient.mk_surjective`).  The loop normal-form child
(`TarchaBraids.every_loop_homotopic_braidWord_v1`, currently Open) supplies a
signed half-twist word `w` and a homotopy to its word loop.  The proved
algebraic bridge (`TarchaBraids.braidWord_free_eval_v1`) identifies the free-
group evaluation of `w` with the quotient class of the word loop, so
`braidWordFree w` is a preimage of the loop class under the free-group lift.

Dependency status: the only Open dep is the topological loop normal form
`0fa0a598-6b37-4d0f-a8f0-f491f0b924bb`; the eval bridge `46bddad7` is Proved.
Expected verdict: SKETCH_ACCEPTED until the normal form lands. -/
theorem solution (n : ℕ) :
    Function.Surjective
      (FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i)) := by
  intro g
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  obtain ⟨w, hw⟩ := TarchaBraids.every_loop_homotopic_braidWord_v1 n γ
  refine ⟨braidWordFree w, ?_⟩
  rw [TarchaBraids.braidWord_free_eval_v1]
  change Path.Homotopic.Quotient.mk (braidWordLoop n w) =
    Path.Homotopic.Quotient.mk γ
  exact (Path.Homotopic.Quotient.eq).2 hw.symm
