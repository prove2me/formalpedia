-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.exponent_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:53:38.188002+00:00
-- url     : https://prove2.me/submissions/4d7ec691-c3ab-47b5-b777-283e8c6a6147

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_exponent_identity_algebraic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j ℓ : ℕ) :
    ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ : ℤ) =
    (↑j + 1) ^ 2 + 2 * ↑(ℓ.choose 2) - 2 * ↑j * ↑ℓ := by
  linarith [Int.natAbs_sq (-(↑j + 1 : ℤ) + ↑ℓ), exponent_identity_algebraic j ℓ]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
