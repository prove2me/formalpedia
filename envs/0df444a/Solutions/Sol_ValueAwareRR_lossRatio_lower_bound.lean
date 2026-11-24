-- Prove2me | solution 1 for ValueAwareRR.lossRatio_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:11:26.222814+00:00
-- url     : https://prove2.me/submissions/e5957f1e-461b-4a91-afe5-52fda3c0681b

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_lossRatio_exact

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (hm : 0 ≤ m) :
    4 * m ^ 2 ≤ lossRatio m := by
  rw [lossRatio_exact]
  nlinarith
end ValueAwareRR
