-- Prove2me | solution 1 for RevenueOrdered.Tightness.tightP_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:17:48.518676+00:00
-- url     : https://prove2.me/submissions/b03ff7dc-30a2-4254-87ca-f305c0c221d0

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
import Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
import Definitions.Def_RevenueOrdered_Tightness_TightInstance

open RevenueOrdered.Tightness in
theorem solution (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (S S' : Finset (TightProduct k)) (hSS' : S ⊆ S') (x : TightProduct k) (hx : x ∈ S) :
    tightP k ε x S' ≤ tightP k ε x S := by
  unfold tightP
  by_cases h : x ∈ S' ∧ ∀ y ∈ S', y.val.1 = x.val.1 → x.val.2.val ≤ y.val.2.val
  · have h2 : x ∈ S ∧ ∀ y ∈ S, y.val.1 = x.val.1 → x.val.2.val ≤ y.val.2.val :=
      ⟨hx, fun y hy => h.2 y (hSS' hy)⟩
    rw [if_pos h, if_pos h2]
  · rw [if_neg h]
    split_ifs <;> positivity
