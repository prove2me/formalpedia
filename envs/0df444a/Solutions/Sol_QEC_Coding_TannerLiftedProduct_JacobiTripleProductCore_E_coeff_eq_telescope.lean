-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.E_coeff_eq_telescope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:55:17.065591+00:00
-- url     : https://prove2.me/submissions/739d7adf-f145-4e9c-a1c4-fa1257fd1390

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_pointwise_telescope
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_T_finite_support
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_W_finite_support
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_AW_finite_support
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finsum_telescope

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j : ℕ) (b : ℤ) :
    E_coeff (A_hahn j) b =
    ∑ᶠ ℓ : ℕ, ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b -
    ∑ᶠ ℓ : ℕ, (A_hahn j * ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ)).coeff b := by
  apply finsum_telescope (T_finite_support j b) (W_finite_support j b) (AW_finite_support j b)
  · simp
  · intro ℓ
    simpa only [HahnSeries.coeff_sub] using congr_arg (·.coeff b) (pointwise_telescope j ℓ)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
