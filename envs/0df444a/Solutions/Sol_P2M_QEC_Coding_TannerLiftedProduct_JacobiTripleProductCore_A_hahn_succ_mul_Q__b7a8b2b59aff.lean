-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_A_hahn_succ_mul_Q__b7a8b2b59aff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:38:45.08081+00:00
-- url     : https://prove2.me/submissions/53449d6e-90be-4064-ae40-fbba581fe83c

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j : ℕ) : A_hahn (j + 1) * Q₀ = A_hahn j := by
  simp only [A_hahn, Q₀]
  rw [HahnSeries.single_mul_single]
  exact congr_arg₂ _ (by push_cast; ring_nf) (one_mul 1)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
