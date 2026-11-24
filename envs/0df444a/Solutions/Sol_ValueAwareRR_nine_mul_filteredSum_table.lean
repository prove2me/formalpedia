-- Prove2me | solution 1 for ValueAwareRR.nine_mul_filteredSum_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:16:15.51703+00:00
-- url     : https://prove2.me/submissions/21aa2ddd-d573-4552-8938-2238a89166da

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (r : Representative) :
    9 * filteredSum m (r, false) = nineFilteredTable m r := by
  cases r <;>
    simp [filteredSum, prefixOne, prefixTwo, prefixThree, orderedResidual,
      residual, orderAt, representativeOrder, contraction, familyA, familyB,
      nineFilteredTable] <;> ring
end ValueAwareRR
