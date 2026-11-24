-- Prove2me | solution 1 for ValueAwareRR.normalizedProxy_diagonal_global_minimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:12:34.190835+00:00
-- url     : https://prove2.me/submissions/3b81ee49-db66-4d92-ab96-a93123814ece

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_proxySelectedOrder_diagonal_global_minimum
import Theorems.Thm_ValueAwareRR_normalizedDiagonalScore_scaling

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    normalizedDiagonalScore m proxySelectedOrder ≤ normalizedDiagonalScore m o := by
  rw [normalizedDiagonalScore_scaling, normalizedDiagonalScore_scaling]
  exact mul_le_mul_of_nonneg_left
    (proxySelectedOrder_diagonal_global_minimum m hm o) (sq_nonneg _)
end ValueAwareRR
