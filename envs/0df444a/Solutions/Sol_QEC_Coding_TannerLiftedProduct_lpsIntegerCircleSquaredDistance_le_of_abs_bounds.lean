-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegerCircleSquaredDistance_le_of_abs_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:36.992486+00:00
-- url     : https://prove2.me/submissions/53ebc54c-5b31-4b6b-a401-a26344868c25

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a b : ℤ × ℤ) (L : ℤ) (hL : 0 ≤ L)
    (hx : |b.1-a.1| ≤ L) (hy : |b.2-a.2| ≤ L) :
    lpsIntegerCircleSquaredDistance a b ≤ 2*L^2 := by
  have hx' : |b.1-a.1|^2 ≤ L^2 := (sq_le_sq₀ (abs_nonneg _) hL).2 hx
  have hy' : |b.2-a.2|^2 ≤ L^2 := (sq_le_sq₀ (abs_nonneg _) hL).2 hy
  unfold lpsIntegerCircleSquaredDistance
  nlinarith [sq_abs (b.1-a.1),sq_abs (b.2-a.2)]
end QEC.Coding.TannerLiftedProduct
