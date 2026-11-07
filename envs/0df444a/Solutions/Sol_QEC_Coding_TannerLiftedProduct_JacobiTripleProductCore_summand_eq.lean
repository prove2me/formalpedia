-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summand_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:52:03.690595+00:00
-- url     : https://prove2.me/submissions/976b2056-c6fd-4406-848d-597e620cb7cd

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_inv_product_eq_qBinom_mul_inv

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {n k : ℕ} (hkn : k ≤ n) :
    aCoeff (n - k) * bCoeff k =
    (-1) ^ n * PowerSeries.invOfUnit (P n) 1 *
      (qBinom (q ^ 2) n k * (-(1 : R)) ^ k * (q ^ 2) ^ k.choose 2) := by
  simp only [aCoeff, bCoeff]
  rw [show (-(1 : R)) ^ k = (-1 : R) ^ k by ring]
  conv_lhs => rw [show (-1 : R) ^ (n - k) * PowerSeries.invOfUnit (P (n - k)) 1 *
      ((q ^ 2) ^ k.choose 2 * PowerSeries.invOfUnit (P k) 1) =
      (-1) ^ (n - k) * (q ^ 2) ^ k.choose 2 *
        (PowerSeries.invOfUnit (P (n - k)) 1 * PowerSeries.invOfUnit (P k) 1) by ring]
  rw [inv_product_eq_qBinom_mul_inv hkn]
  have hkk : (-1 : R) ^ k * (-1) ^ k = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨k, rfl⟩
  rw [show (-1 : R) ^ (n - k) = (-1) ^ n * (-1) ^ k by
    calc (-1 : R) ^ (n - k) = (-1) ^ (n - k) * ((-1) ^ k * (-1) ^ k) := by rw [hkk, mul_one]
      _ = _ := by rw [← mul_assoc,
          show (-1 : R) ^ (n - k) * (-1) ^ k = (-1) ^ n from
            (pow_add (-1 : R) (n - k) k).symm ▸ congrArg ((-1 : R) ^ ·) (by omega)]]
  ring
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
