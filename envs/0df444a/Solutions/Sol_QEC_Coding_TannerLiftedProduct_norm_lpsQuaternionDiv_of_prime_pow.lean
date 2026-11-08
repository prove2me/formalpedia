-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.norm_lpsQuaternionDiv_of_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:42:43.380216+00:00
-- url     : https://prove2.me/submissions/af5a3877-3d6b-4633-8460-a3e37c1eec1e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsScaleQuaternion_div_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : p.Prime) {n : ℕ} {t : LPSQuaternion}
    (hdiv : t.CoordinatesDvd (p : ℤ))
    (hnorm : t.norm = (p : ℤ) ^ (n + 2)) :
    (lpsQuaternionDiv (p : ℤ) t).norm = (p : ℤ) ^ n := by
  let u := lpsQuaternionDiv (p : ℤ) t
  have hscale : lpsScaleQuaternion (p : ℤ) u = t :=
    lpsScaleQuaternion_div_eq hdiv
  have hnormScale := congrArg LPSQuaternion.norm hscale
  rw [norm_lpsScaleQuaternion, hnorm] at hnormScale
  have hpSqNe : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  apply mul_left_cancel₀ hpSqNe
  calc
    (p : ℤ) ^ 2 * (lpsQuaternionDiv (p : ℤ) t).norm =
        (p : ℤ) ^ (n + 2) := hnormScale
    _ = (p : ℤ) ^ 2 * (p : ℤ) ^ n := by ring
end QEC.Coding.TannerLiftedProduct
