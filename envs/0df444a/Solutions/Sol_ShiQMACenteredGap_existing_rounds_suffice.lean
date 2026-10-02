-- Prove2me | solution 1 for ShiQMACenteredGap.existing_rounds_suffice
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-02T01:41:43.959467+00:00
-- url     : https://prove2.me/submissions/1220b555-4238-43c2-9168-63095dc55e0d

import Definitions.Def_ShiQMACenteredGapDominatingSchedule
import Theorems.Thm_ShiQMACenteredGap_generalGapRounds_suffice
import Theorems.Thm_ShiQMACenteredGap_biasIter_rounds_mono
import Theorems.Thm_ShiQMACenteredGap_generalGapRounds_le_existing

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem solution {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1 / 2)
    (q p : Polynomial ℕ) (n : Nat) (hgap : (1 / 6 : ℝ) ≤ (↑(q.eval n) : ℝ) * d) :
    1 / 2 - ((1 : ℝ) / 2) ^ (p.eval n) ≤
      biasIter d (rounds (gapPolynomial q p) n) :=
  (generalGapRounds_suffice hd₀ hd₁ q p n hgap).trans
    (biasIter_rounds_mono hd₀ hd₁ (generalGapRounds_le_existing q p n))
