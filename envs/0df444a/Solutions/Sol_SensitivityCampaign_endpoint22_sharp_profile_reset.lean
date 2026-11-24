-- Prove2me | solution 1 for SensitivityCampaign.endpoint22_sharp_profile_reset
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-24T07:51:30.839474+00:00
-- url     : https://prove2.me/submissions/fcce1a98-9016-4511-899b-29442f7bec23

import Definitions.Def_Sensitivity213981Formal_Endpoint22NumericData
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_NatTable_dominates_sound
open Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22
open Sensitivity213981Formal.ThreeBoundFullProfile
open Sensitivity213981Formal.ThreeBoundNumeric

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

private def times (k : ℕ) : NatTable → NatTable
  | .leaf x => .leaf (k * x)
  | .branch i a b => .branch i (times k a) (times k b)

private theorem times_get (k : ℕ) (t : NatTable) (i : ℕ) :
    (times k t).get i = k * t.get i := by
  induction t with
  | leaf x => rfl
  | branch cut a b ha hb =>
    simp only [times, NatTable.get]
    split <;> assumption

private theorem resetCheck :
    NatTable.dominates 3487007904161347435 (times 344500417784 profileTable4) profileTable0
      = true := by decide +kernel

private theorem profile_le (coord : Coord 22) :
    344500417784 * profile4 coord ≤ 3487007904161347435 * profile0 coord := by
  have h := NatTable.dominates_sound _ _ _ resetCheck (flatIndex coord)
  rw [times_get] at h
  exact h

theorem solution : (∀ c : Coord 22, 344500417784 * profile4 c ≤ 3487007904161347435 * profile0 c) ∧
    344500417784 * profileTable4.get 2284 = 3487007904161347435 * profileTable0.get 2284 ∧
    0 < profileTable0.get 2284 :=
  ⟨profile_le, by decide +kernel, by decide +kernel⟩
