-- Prove2me | solution 1 for ValueAwareRR.normalizedDiagonalScore_minimizer_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:12:25.566103+00:00
-- url     : https://prove2.me/submissions/c52d4da5-9b95-4508-b086-47f6dc56e8b4

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_diagonalScore_minimizer_iff
import Theorems.Thm_ValueAwareRR_normalizationScale_pos
import Theorems.Thm_ValueAwareRR_normalizedDiagonalScore_scaling

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    normalizedDiagonalScore m o = normalizedDiagonalScore m proxySelectedOrder ↔
      o = proxySelectedOrder ∨ o = signReverse proxySelectedOrder := by
  rw [normalizedDiagonalScore_scaling, normalizedDiagonalScore_scaling]
  have hs2 : 0 < normalizationScale m ^ 2 := sq_pos_of_pos (normalizationScale_pos m hm)
  constructor
  · intro h
    apply (diagonalScore_minimizer_iff m hm o).mp
    nlinarith
  · intro h
    rw [(diagonalScore_minimizer_iff m hm o).mpr h]
end ValueAwareRR
