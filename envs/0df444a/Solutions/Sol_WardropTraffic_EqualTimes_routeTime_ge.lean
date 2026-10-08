-- Prove2me | solution 1 for WardropTraffic.EqualTimes.routeTime_ge
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:30:08.104559+00:00
-- url     : https://prove2.me/submissions/5cd6dcac-b9e1-4ea5-98c0-ed1281c1456a

import Mathlib
import Definitions.Def_WardropTraffic_EqualTimes_Setting
open WardropTraffic.EqualTimes

theorem solution {D : ℕ} (b p : Fin D → ℝ) (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i)
    (i : Fin D) (x : ℝ) (hx0 : 0 ≤ x) (hxp : x < p i) :
    b i ≤ routeTime b p i x ∧ (routeTime b p i x = b i ↔ x = 0) := by
  have hd : 0 < 1 - x / p i := sub_pos.mpr ((div_lt_one (hp i)).mpr hxp)
  have hq : 0 ≤ x / p i := div_nonneg hx0 (hp i).le
  unfold routeTime
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [hb i]
  · rw [div_eq_iff hd.ne']
    constructor
    · intro h
      have : x / p i = 0 := by nlinarith [hb i]
      exact (div_eq_zero_iff).mp this |>.resolve_right (hp i).ne'
    · intro h
      simp [h]


#print axioms solution
