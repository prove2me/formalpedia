-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_G_support_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:38:11.796403+00:00
-- url     : https://prove2.me/submissions/eef165a0-244e-4313-806d-1ae11cc99916

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_G_vanishes_of_lt

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j d : ℕ) :
    (Function.support fun ℓ : ℕ =>
      (PowerSeries.coeff d)
        ((-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
         PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1)).Finite := by
  apply (Set.finite_Iio (d + 1)).subset
  intro ℓ hℓ
  simp only [Set.mem_Iio]
  by_contra h_le
  push_neg at h_le
  exact hℓ (coeff_G_vanishes_of_lt j ℓ d
    (lt_of_lt_of_le d.lt_succ_self (le_trans h_le (Nat.le_add_left ℓ _))))
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
