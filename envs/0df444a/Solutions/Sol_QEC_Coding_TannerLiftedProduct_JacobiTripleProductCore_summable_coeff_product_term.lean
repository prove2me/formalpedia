-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_coeff_product_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:49:43.013243+00:00
-- url     : https://prove2.me/submissions/460dd684-3cd6-4981-bddd-cf857d90b880

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_tendsto_top
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_exists_bound_for_order
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_mul_eq_zero_of_order_gt

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {x : R} (hx : x.constantCoeff = 0)
    (p q : S) (d : ℕ) :
    Summable (fun (kl : ℕ × ℕ) =>
      (PowerSeries.coeff d)
        ((p.coeff kl.1 * x ^ kl.1) * (q.coeff kl.2 * x ^ kl.2))) := by
  have hp := order_tendsto_top hx p
  have hq := order_tendsto_top hx q
  obtain ⟨Np, hNp⟩ := exists_bound_for_order hp d
  obtain ⟨Nq, hNq⟩ := exists_bound_for_order hq d
  apply summable_of_ne_finset_zero (s := Finset.range Np ×ˢ Finset.range Nq)
  intro ⟨k, l⟩ hkl
  simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hkl
  apply coeff_mul_eq_zero_of_order_gt
  rcases hkl with hk | hl
  · exact Or.inl (hNp k hk)
  · exact Or.inr (hNq l hl)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
