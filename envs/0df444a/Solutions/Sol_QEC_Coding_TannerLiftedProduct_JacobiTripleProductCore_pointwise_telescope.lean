-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.pointwise_telescope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:53:28.247347+00:00
-- url     : https://prove2.me/submissions/87d1d118-4012-42b3-bd8b-cd6d85b5212c

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_V_recurrence
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_Q__pow_fc719b7707f4

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j ℓ : ℕ) :
    (-A_hahn j) ^ (ℓ + 1) * Q₀ ^ ((ℓ + 1).choose 2) * V (ℓ + 1) =
    (-(A_hahn j * Q₀)) ^ (ℓ + 1) * Q₀ ^ ((ℓ + 1).choose 2) * V (ℓ + 1) -
    A_hahn j * ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ) := by
  rw [neg_A_Q₀_pow j (ℓ + 1), neg_A_Q₀_pow j ℓ,
    show (ℓ + 1).choose 2 = ℓ.choose 2 + ℓ from by simp [Nat.choose_succ_succ, add_comm],
    pow_add, V_recurrence ℓ]
  ring
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
