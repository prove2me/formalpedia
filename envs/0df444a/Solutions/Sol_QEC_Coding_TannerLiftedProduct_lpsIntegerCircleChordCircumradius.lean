-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegerCircleChordCircumradius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:49:16.117102+00:00
-- url     : https://prove2.me/submissions/efe9a633-32ae-4151-a026-65ee27d76dba

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
    (a b c : ℤ × ℤ) (n : ℤ)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n) (hc : c.1^2+c.2^2=n) :
    4*n*(lpsIntegerCircleChordDet a b c)^2 =
      lpsIntegerCircleSquaredDistance a b * lpsIntegerCircleSquaredDistance a c *
        lpsIntegerCircleSquaredDistance b c := by
  have hu : 2*(a.1*(b.1-a.1)+a.2*(b.2-a.2)) =
      -((b.1-a.1)^2+(b.2-a.2)^2) := by nlinarith [ha,hb]
  have hv : 2*(a.1*(c.1-a.1)+a.2*(c.2-a.2)) =
      -((c.1-a.1)^2+(c.2-a.2)^2) := by nlinarith [ha,hc]
  calc
    4*n*(lpsIntegerCircleChordDet a b c)^2 =
        (2*(a.1*(b.1-a.1)+a.2*(b.2-a.2)))^2 * ((c.1-a.1)^2+(c.2-a.2)^2) -
        2*(2*(a.1*(b.1-a.1)+a.2*(b.2-a.2))) *
          (2*(a.1*(c.1-a.1)+a.2*(c.2-a.2))) *
          ((b.1-a.1)*(c.1-a.1)+(b.2-a.2)*(c.2-a.2)) +
        (2*(a.1*(c.1-a.1)+a.2*(c.2-a.2)))^2 * ((b.1-a.1)^2+(b.2-a.2)^2) := by
      rw [← ha]
      unfold lpsIntegerCircleChordDet
      ring
    _ = lpsIntegerCircleSquaredDistance a b * lpsIntegerCircleSquaredDistance a c *
        lpsIntegerCircleSquaredDistance b c := by
      rw [hu,hv]
      unfold lpsIntegerCircleSquaredDistance
      ring
end QEC.Coding.TannerLiftedProduct
