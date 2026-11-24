-- Prove2me | solution 1 for ValueAwareRR.normalizedLossRatio_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:17:28.904358+00:00
-- url     : https://prove2.me/submissions/eb39affa-6336-43fb-9e96-a14dc2d946c1

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_lossRatio_lower_bound
import Theorems.Thm_ValueAwareRR_normalizedLossRatio_eq_lossRatio

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (hm : 2 ≤ m) :
    4 * m ^ 2 ≤ normalizedLossRatio m := by
  rw [normalizedLossRatio_eq_lossRatio m hm]
  exact lossRatio_lower_bound m (by linarith)
end ValueAwareRR
