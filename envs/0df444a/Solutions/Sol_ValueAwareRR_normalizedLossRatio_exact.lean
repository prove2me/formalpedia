-- Prove2me | solution 1 for ValueAwareRR.normalizedLossRatio_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:17:29.466589+00:00
-- url     : https://prove2.me/submissions/118bf32a-f289-4cfa-90f3-ee6526d76e4f

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_lossRatio_exact
import Theorems.Thm_ValueAwareRR_normalizedLossRatio_eq_lossRatio

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (hm : 2 ≤ m) :
    normalizedLossRatio m = (10 * m + 3) ^ 2 / 25 := by
  rw [normalizedLossRatio_eq_lossRatio m hm, lossRatio_exact]
end ValueAwareRR
