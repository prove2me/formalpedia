-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.norm_lpsQuaternionDiv_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:49:46.441056+00:00
-- url     : https://prove2.me/submissions/58834c92-bc9d-469e-b221-0fbfc861c72e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionDiv_mul_conj_mul_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : p.Prime) {n : ℕ} {t beta : LPSQuaternion}
    (ht : t.norm = (p : ℤ) ^ (n + 1))
    (hbeta : beta.norm = p)
    (hdiv : (t * beta.conj).CoordinatesDvd (p : ℤ)) :
    (lpsQuaternionDiv (p : ℤ) (t * beta.conj)).norm =
      (p : ℤ) ^ n := by
  let u := lpsQuaternionDiv (p : ℤ) (t * beta.conj)
  have hfactor : u * beta = t :=
    lpsQuaternionDiv_mul_conj_mul_eq hp hbeta hdiv
  have hnorm := congrArg LPSQuaternion.norm hfactor
  rw [LPSQuaternion.norm_mul, ht, hbeta] at hnorm
  have hpNe : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  apply mul_right_cancel₀ hpNe
  calc
    (lpsQuaternionDiv (p : ℤ) (t * beta.conj)).norm * (p : ℤ) =
        (p : ℤ) ^ (n + 1) := hnorm
    _ = (p : ℤ) ^ n * (p : ℤ) := by rw [pow_succ]
end QEC.Coding.TannerLiftedProduct
