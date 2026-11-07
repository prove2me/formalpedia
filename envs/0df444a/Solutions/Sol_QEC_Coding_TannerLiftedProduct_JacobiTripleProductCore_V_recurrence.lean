-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.V_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:39:48.90271+00:00
-- url     : https://prove2.me/submissions/f7e29843-215c-4d87-b0e5-8dccd0697b05

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_invOfUnit_factor
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___factor_eq_03466fa1241f

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (ℓ : ℕ) :
    V ℓ = V (ℓ + 1) * (1 - Q₀ ^ (ℓ + 1)) := by
  show ι_hahn (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    ι_hahn (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) (ℓ + 1)) 1) * (1 - Q₀ ^ (ℓ + 1))
  rw [invOfUnit_factor ℓ, map_mul, ι_factor_eq]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
