-- Prove2me | solution 1 for ValueAwareRR.exactLoss_cast_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:13:51.766601+00:00
-- url     : https://prove2.me/submissions/df4557e0-8948-4a3e-acab-bb88656f3f4e

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_exactLoss_eq_filtered_square

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    ((exactLoss m o : ℚ) : ℝ) = ((filteredSum m o : ℚ) : ℝ) ^ 2 / 162 := by
  exact_mod_cast exactLoss_eq_filtered_square m o
end ValueAwareRR
