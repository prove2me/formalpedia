-- Prove2me | solution 1 for StrategicInventory.Sequential.stage3_best_response
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T15:38:11.007233+00:00
-- url     : https://prove2.me/submissions/a939a3ba-4fd4-4baf-afb3-a1fc916fa1f6

import Mathlib
import Definitions.Def_StrategicInventory_Sequential_Game
import Definitions.Def_StrategicInventory_Sequential_IsSPE

open StrategicInventory.Sequential in
theorem solution (α h s : ℝ) (hα : 0 < α) (hh : 0 ≤ h) (hs : 0 ≤ s)
    (σ : Profile) (hσ : IsSPE α h s σ)
    (w1 Q1 q1 w2 Q2 q2 : ℝ) (hw1 : 0 ≤ w1) (hq1 : 0 ≤ q1) (hq1Q1 : q1 ≤ Q1)
    (hw2 : 0 ≤ w2) (hQ2 : 0 ≤ Q2) (hq2 : 0 ≤ q2) (hq2I : q2 ≤ (Q1 - q1) + Q2) :
    σ.direct w1 Q1 q1 w2 Q2 q2 = max (α - q2 - s) 0 / 2 := by
  obtain ⟨hx0, hopt⟩ := hσ.1 w1 Q1 q1 w2 Q2 q2 hw1 hq1 hq1Q1 hw2 hQ2 hq2 hq2I
  set x := σ.direct w1 Q1 q1 w2 Q2 q2 with hxdef
  have key : ∀ qs : ℝ, 0 ≤ qs →
      (α - q2 - qs - s) * qs ≤ (α - q2 - x - s) * x := by
    intro qs hqs
    have := hopt qs hqs
    simp only [supplierPayoff, Profile.outcomeAtDirect] at this
    rw [← hxdef] at this
    linarith
  rcases le_or_gt 0 (α - q2 - s) with hc | hc
  · rw [max_eq_left hc]
    have h1 := key ((α - q2 - s) / 2) (by linarith)
    have hsq : (x - (α - q2 - s) / 2) ^ 2 ≤ 0 := by nlinarith
    have : (x - (α - q2 - s) / 2) ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · rw [max_eq_right hc.le]
    have h1 := key 0 le_rfl
    rcases hx0.lt_or_eq with hxp | hxe
    · nlinarith
    · rw [← hxe]; norm_num
