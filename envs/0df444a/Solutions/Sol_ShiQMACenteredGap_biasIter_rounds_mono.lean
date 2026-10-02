-- Prove2me | solution 1 for ShiQMACenteredGap.biasIter_rounds_mono
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-02T01:32:47.829505+00:00
-- url     : https://prove2.me/submissions/6eb73f84-f44a-49ee-91c0-fc5e0fd23c6d

import Definitions.Def_ShiQMACenteredGapDominatingSchedule
import Theorems.Thm_ShiQMACenteredGap_biasStep_ge
import Theorems.Thm_ShiQMACenteredGap_biasIter_bounds

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem solution {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1 / 2)
    {r s : Nat} (hrs : r ≤ s) : biasIter d r ≤ biasIter d s := by
  apply monotone_nat_of_le_succ _ hrs
  intro k
  exact biasStep_ge (biasIter_bounds hd₀ hd₁ k).1 (biasIter_bounds hd₀ hd₁ k).2
