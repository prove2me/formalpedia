-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.telescope_rewrite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:38:30.367991+00:00
-- url     : https://prove2.me/submissions/747bad62-aa89-44d1-a8c2-1c41e60b779b

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {G_type : Type*} [AddCommGroup G_type]
    {t w u : ℕ → G_type}
    (N_val : ℕ)
    (h_zero : t 0 = w 0)
    (h_succ : ∀ ℓ, t (ℓ + 1) = w (ℓ + 1) - u ℓ) :
    ∑ i ∈ Finset.range (N_val + 1), t i =
    ∑ i ∈ Finset.range (N_val + 1), w i - ∑ i ∈ Finset.range N_val, u i := by
  induction N_val with
  | zero => simp [h_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp_all [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
    abel
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
