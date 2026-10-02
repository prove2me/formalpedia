-- Prove2me | solution 1 for ShiQMACenteredGap.generalGapRounds_suffice
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-02T00:23:44.885669+00:00
-- url     : https://prove2.me/submissions/566ebbed-ff24-4e0a-b973-d389e726b87c

import Definitions.Def_ShiQMACenteredGapGeneralSchedule
import Theorems.Thm_ShiQMACenteredGap_normalizationRounds_suffice
import Theorems.Thm_ShiQMACenteredGap_biasIter_mono
import Theorems.Thm_ShiQMACenteredGap_biasIter_add
import Theorems.Thm_ShiQMACenteredGap_biasIter_standard
import Theorems.Thm_ShiQMACenteredGap_biasIter_bounds
import Theorems.Thm_ShiQMAConstructiveSchedule_error_rounds

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem solution {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2)
    (q p : Polynomial ℕ) (n : Nat) (hgap : (1 / 6 : ℝ) ≤ (↑(q.eval n) : ℝ) * d) :
    1 / 2 - ((1 : ℝ) / 2) ^ (p.eval n) ≤ biasIter d (generalGapRounds q p n) := by
  have hn := normalizationRounds_suffice hd hd' q n hgap
  have hm := biasIter_mono (by norm_num : (0 : ℝ) ≤ 1 / 6) hn
    (biasIter_bounds hd hd' (normalizationRounds q n)).2 (rounds p n)
  rw [biasIter_standard] at hm
  rw [generalGapRounds, biasIter_add]
  have he := error_rounds p n
  linarith
