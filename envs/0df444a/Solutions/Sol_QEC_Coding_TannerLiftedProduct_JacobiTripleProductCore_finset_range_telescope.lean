-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finset_range_telescope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:39:59.051547+00:00
-- url     : https://prove2.me/submissions/38f3b5b7-4789-4aa0-b4fa-3ec954770552

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_telescope_rewrite

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {G_type : Type*} [AddCommGroup G_type]
    {t w u : ℕ → G_type}
    (N_val : ℕ)
    (ht_van : t (N_val + 1) = 0)
    (hw_van : w (N_val + 1) = 0)
    (h_zero : t 0 = w 0)
    (h_succ : ∀ ℓ, t (ℓ + 1) = w (ℓ + 1) - u ℓ) :
    ∑ i ∈ Finset.range (N_val + 1), t i =
    ∑ i ∈ Finset.range (N_val + 1), w i - ∑ i ∈ Finset.range (N_val + 1), u i := by
  rw [telescope_rewrite N_val h_zero h_succ]
  congr 1
  rw [Finset.sum_range_succ, show u N_val = 0 by
    have := h_succ N_val
    rw [ht_van, hw_van, zero_sub] at this
    exact neg_eq_zero.mp this.symm, add_zero]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
