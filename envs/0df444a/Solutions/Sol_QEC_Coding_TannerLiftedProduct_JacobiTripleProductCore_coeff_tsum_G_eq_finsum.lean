-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_tsum_G_eq_finsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:39:48.054995+00:00
-- url     : https://prove2.me/submissions/6b260ff5-64cc-47bd-9231-dc62d110037a

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_G_summable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_G_support_finite

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j d : ℕ) : letI := piTop;
    (PowerSeries.coeff d) (∑' ℓ : ℕ,
      (-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    ∑ᶠ ℓ : ℕ, (PowerSeries.coeff d)
      ((-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) := by
  letI := piTop
  rw [Summable.map_tsum (G_summable j) (PowerSeries.coeff d)
    (PowerSeries.WithPiTopology.continuous_coeff (LaurentPolynomial ℤ) d)]
  exact tsum_eq_finsum (coeff_G_support_finite j d)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
