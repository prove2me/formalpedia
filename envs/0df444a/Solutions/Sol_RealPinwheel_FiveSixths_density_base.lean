-- Prove2me | solution 1 for RealPinwheel.FiveSixths.density_base
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:16:43.434461+00:00
-- url     : https://prove2.me/submissions/7f682b06-a159-4eae-bb70-be1383eba4d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RealPinwheel_FiveSixths_bounded_density_base
open RealPinwheel.FiveSixths
theorem solution {n : ℕ} (A : Instance n) (hn : n ≤ 8)
    (hD : density A ≤ (5 : ℝ) / 6) : Schedulable A.period := by
  obtain ⟨L, S, hL, hbound, hperiod, hvalid⟩ := bounded_density_base A hn hD
  exact ⟨S, hvalid⟩
