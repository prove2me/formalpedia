-- Prove2me | solution 1 for PermanentRollout.squareFreeMonomial_quotient_eq_variable_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/7f5baefd-27ef-4ef8-b627-9d3b0a554954

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (r : ℕ) (rows : Finset (Fin r)) :
    Ideal.Quotient.mk (squareZeroIdeal r) (squareFreeMonomial rows) =
      ∏ i ∈ rows, squareZeroVariable r i := by
  simp [squareFreeMonomial, squareZeroVariable]
end PermanentRollout
