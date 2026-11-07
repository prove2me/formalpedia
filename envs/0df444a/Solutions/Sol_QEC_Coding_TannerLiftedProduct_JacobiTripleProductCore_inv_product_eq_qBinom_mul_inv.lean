-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.inv_product_eq_qBinom_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:50:25.783527+00:00
-- url     : https://prove2.me/submissions/a4468588-22c5-420e-bbed-3d3e4945c303

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_mul_qPoch
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_mul_invOfUnit_cancel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_constantCoeff_P_eq_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {n k : ℕ} (hkn : k ≤ n) :
    PowerSeries.invOfUnit (P (n - k)) 1 * PowerSeries.invOfUnit (P k) 1 =
    qBinom (q ^ 2) n k * PowerSeries.invOfUnit (P n) 1 := by
  have hP_unit : ∀ m, IsUnit (P m) :=
    fun m ↦ PowerSeries.isUnit_iff_constantCoeff.mpr
      (by rw [constantCoeff_P_eq_one]; exact isUnit_one)
  have hcancel : ∀ m, PowerSeries.invOfUnit (P m) 1 * P m = 1 :=
    fun m ↦ PowerSeries.invOfUnit_mul _ _ (by rw [constantCoeff_P_eq_one]; rfl)
  apply (hP_unit k).mul (hP_unit (n - k)) |>.mul_right_cancel
  calc PowerSeries.invOfUnit (P (n - k)) 1 * PowerSeries.invOfUnit (P k) 1 *
      (P k * P (n - k))
      = PowerSeries.invOfUnit (P (n - k)) 1 * (PowerSeries.invOfUnit (P k) 1 * P k) *
          P (n - k) := by ring
    _ = 1 := by rw [hcancel k, mul_one, hcancel (n - k)]
    _ = qBinom (q ^ 2) n k * P k * P (n - k) * PowerSeries.invOfUnit (P n) 1 := by
          rw [qBinom_mul_qPoch _ _ _ hkn, qPoch_mul_invOfUnit_cancel n]
    _ = qBinom (q ^ 2) n k * PowerSeries.invOfUnit (P n) 1 *
          (P k * P (n - k)) := by ring
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
