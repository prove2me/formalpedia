-- Prove2me | solution 1 for TurnTables.Reciprocal.offeree_response
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T00:51:31.881568+00:00
-- url     : https://prove2.me/submissions/4c618096-0ce1-42bb-8d6f-9b53f15b9c64

import Mathlib
import Definitions.Def_TurnTables_Reciprocal_Model

open TurnTables.Reciprocal in
theorem solution (P : Params) (hP : P.Standing) :
    ¬ Reciprocates P .part (strikeB P) ∧
      Reciprocates P .full (strikeB P) := by
  obtain ⟨hγ0, hγ1, hV1, hV2⟩ := hP
  simp only [Reciprocates, strikeB, Impl.val]
  refine ⟨?_, ?_⟩
  · intro h; linarith
  · have hV : 0 < P.V2 := by linarith
    nlinarith
