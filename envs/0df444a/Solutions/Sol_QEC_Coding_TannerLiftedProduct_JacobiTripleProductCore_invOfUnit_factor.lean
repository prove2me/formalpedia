-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.invOfUnit_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:38:12.812542+00:00
-- url     : https://prove2.me/submissions/5776dfef-1dbe-49ed-8ab5-ac59536763a6

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_constantCoeff_qPoch_eq_one
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_succ__251408f0b858
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_isUnit_qPoch
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_last_factor_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (ℓ : ℕ) :
    PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 =
    PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) (ℓ + 1)) 1 *
      (1 - q ^ (2 * (↑ℓ + 1))) := by
  have hcc : ∀ m, PowerSeries.constantCoeff (qPoch (q ^ 2) (q ^ 2) m : R) =
      ↑(1 : (LaurentPolynomial ℤ)ˣ) := fun m => by simp [constantCoeff_qPoch_eq_one]
  apply (isUnit_qPoch ℓ).mul_right_cancel
  rw [mul_comm (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) _,
      PowerSeries.mul_invOfUnit _ _ (hcc ℓ), mul_assoc]
  conv_rhs => rw [← qPoch_last_factor_eq]
  rw [mul_comm (1 - q ^ 2 * (q ^ 2) ^ ℓ) _, ← qPoch_succ', PowerSeries.invOfUnit_mul _ _ (hcc (ℓ + 1))]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
