-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_F_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:16:42.232211+00:00
-- url     : https://prove2.me/submissions/25b4b2c0-a1c2-44ff-bbc8-3a392291655d

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_F_ge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (z : ℤ) (ℓ : ℕ) (d : ℕ) (h : d < (z + ↑ℓ).natAbs ^ 2 + ℓ) :
    (PowerSeries.coeff d) (F (z, ℓ)) = 0 :=
  PowerSeries.coeff_of_lt_order _ (Nat.cast_lt.mpr h |>.trans_le (order_F_ge z ℓ))
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
