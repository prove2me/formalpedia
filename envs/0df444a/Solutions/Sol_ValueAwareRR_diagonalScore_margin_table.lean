-- Prove2me | solution 1 for ValueAwareRR.diagonalScore_margin_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:59:27.13971+00:00
-- url     : https://prove2.me/submissions/d1b83838-8b87-4558-b26f-9f9cd30bca92

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (r : Representative) :
    81 * (diagonalScore m (r, false) -
      diagonalScore m proxySelectedOrder) = diagonalMarginTable m r := by
  cases r <;>
    simp [diagonalScore, prefixOne, prefixTwo, prefixThree, orderedResidual,
      residual, orderAt, representativeOrder, contraction, familyA, familyB,
      proxySelectedOrder, diagonalMarginTable] <;> ring
end ValueAwareRR
