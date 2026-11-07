-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_neg_support_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:53:56.728085+00:00
-- url     : https://prove2.me/submissions/612daf64-1748-4622-bc6a-4ad66a29fefb

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finite_support_set

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (d : ℕ) :
    Set.Finite {p : ℕ × ℕ | (-(↑p.1 + 1 : ℤ) + ↑p.2).natAbs ^ 2 + p.2 ≤ d} := by
  rw [show {p : ℕ × ℕ | (-(↑p.1 + 1 : ℤ) + ↑p.2).natAbs ^ 2 + p.2 ≤ d} =
      (fun p : ℕ × ℕ => (-(↑p.1 + 1 : ℤ) + ↑p.2, p.2)) ⁻¹'
        {p : ℤ × ℕ | p.1.natAbs ^ 2 + p.2 ≤ d} by ext ⟨j, ℓ⟩; simp]
  exact (finite_support_set d).preimage (fun ⟨j₁, ℓ₁⟩ _ ⟨j₂, ℓ₂⟩ _ h => by
    simp at h; ext <;> omega)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
