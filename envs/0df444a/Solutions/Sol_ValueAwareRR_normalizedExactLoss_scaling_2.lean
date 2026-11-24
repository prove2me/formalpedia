-- Prove2me | solution 2 for ValueAwareRR.normalizedExactLoss_scaling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:12:41.206384+00:00
-- url     : https://prove2.me/submissions/17d603d9-d710-4416-9cb2-51cb7555dac6

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_normalizedFilteredSum_scaling

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    normalizedExactLoss m o = normalizationScale m ^ 2 * exactLoss m o := by
  rw [normalizedExactLoss, normalizedFilteredSum_scaling, exactLoss]
  simp only [terminalLossFromFiltered]
  ring
end ValueAwareRR
