-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finsum_telescope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:53:35.785534+00:00
-- url     : https://prove2.me/submissions/492fe3fe-8181-4c6d-ae22-7d3503c5b1ca

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finset_range_telescope
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_exists_common_vanishing_bound

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {G_type : Type*} [AddCommGroup G_type]
    {t w u : ℕ → G_type}
    (ht : (Function.support t).Finite)
    (hw : (Function.support w).Finite)
    (hu : (Function.support u).Finite)
    (h_zero : t 0 = w 0)
    (h_succ : ∀ ℓ, t (ℓ + 1) = w (ℓ + 1) - u ℓ) :
    ∑ᶠ ℓ, t ℓ = ∑ᶠ ℓ, w ℓ - ∑ᶠ ℓ, u ℓ := by
  obtain ⟨N, hN⟩ := exists_common_vanishing_bound ht hw hu
  have mk_sub : ∀ (f : ℕ → G_type), (∀ i, N < i → f i = 0) →
      Function.support f ⊆ ↑(Finset.range (N + 1)) :=
    fun f hf x hx => by
      simp
      by_contra h
      exact hx (hf x (by omega))
  rw [finsum_eq_sum_of_support_subset t (mk_sub t (fun i hi => (hN i hi).1)),
      finsum_eq_sum_of_support_subset w (mk_sub w (fun i hi => (hN i hi).2.1)),
      finsum_eq_sum_of_support_subset u (mk_sub u (fun i hi => (hN i hi).2.2))]
  exact finset_range_telescope N ((hN (N + 1) (by omega)).1) ((hN (N + 1) (by omega)).2.1) h_zero h_succ
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
