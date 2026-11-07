-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.expand_shifted_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:58:24.478732+00:00
-- url     : https://prove2.me/submissions/06956c19-0e8e-40bc-af52-1372325aa82c

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_euler_product
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_extract_sign

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k : ℕ) : letI := piTop;
    qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) =
    ∑' ℓ : ℕ, (-1) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 := by
  letI := piTop
  rw [show q ^ 2 * (q ^ 2) ^ k = q ^ (2 + 2 * k) by ring,
      show q ^ (2 + 2 * k) = -(-q ^ (2 * k + 1)) * q by
        simp only [neg_neg]; rw [show (2 + 2 * k : ℕ) = 2 * k + 1 + 1 by omega, pow_succ],
      euler_product (-q ^ (2 * k + 1))]
  exact tsum_congr fun ℓ => by
    rw [extract_sign, show q ^ (ℓ ^ 2) * ((-1 : R) ^ ℓ * q ^ (ℓ * (2 * k + 1))) =
        (-1) ^ ℓ * (q ^ (ℓ ^ 2) * q ^ (ℓ * (2 * k + 1))) by ring, ← pow_add]
    congr 1
    ring
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
