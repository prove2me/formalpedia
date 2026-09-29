-- Prove2me | solution 1 for TarchaBraids.geom_braid_word_relation_sound_v1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T11:53:43.044589+00:00
-- url     : https://prove2.me/submissions/64cea64a-53b2-47fd-b10d-153cb31e1f57
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1
import Theorems.Thm_TarchaBraids_geom_null_word_has_contextual_relator_trace_v1
import Theorems.Thm_TarchaBraids_presented_geom_relator_trace_eq_one_v1

open BraidsLinksMCG TarchaBraids

theorem solution
    (n : ℕ)
    (w : FreeGroup (Fin (n - 1)))
    (hw : FreeGroup.lift
      (fun i : Fin (n - 1) => halfTwistBraid n i) w = 1) :
    PresentedGroup.mk (braidRels n) w = 1 := by
  apply presented_geom_relator_trace_eq_one_v1
  exact geom_null_word_has_contextual_relator_trace_v1 n w hw
