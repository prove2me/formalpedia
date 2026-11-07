-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_G_vanishes_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:53:57.583094+00:00
-- url     : https://prove2.me/submissions/54ebbe54-a9cd-4401-81ca-78bc5e9af53a

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_G_term_ge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j ℓ d : ℕ) (h : d < N_exp j ℓ) :
    (PowerSeries.coeff d)
      ((-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) = 0 :=
  PowerSeries.coeff_of_lt_order d (lt_of_lt_of_le (by exact_mod_cast h) (order_G_term_ge j ℓ))
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
