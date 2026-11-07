-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_tsum_G_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:59:58.509691+00:00
-- url     : https://prove2.me/submissions/0822d209-a9b8-46ed-854b-a97951313812

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_tsum_G_eq_finsum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_functional_equation
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_A_hahn_succ_mul_Q__b7a8b2b59aff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_per_term_coeff_eq
section
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
open PowerSeries
private lemma E_coeff_A_hahn_eq_zero (j : ℕ) (b : ℤ) : E_coeff (A_hahn j) b = 0 := by
  induction j generalizing b with
  | zero => rw [functional_equation 0 b]; simp [show A_hahn 0 = 1 from by simp [A_hahn]]
  | succ j ih =>
    rw [functional_equation (j + 1) b, A_hahn_succ_mul_Q₀]
    simp [ih]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j d : ℕ) : letI := piTop;
    (PowerSeries.coeff d) (∑' ℓ : ℕ,
      (-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) = 0 := by
  rw [coeff_tsum_G_eq_finsum j d, finsum_congr fun ℓ => per_term_coeff_eq j d ℓ]
  exact E_coeff_A_hahn_eq_zero j _
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
