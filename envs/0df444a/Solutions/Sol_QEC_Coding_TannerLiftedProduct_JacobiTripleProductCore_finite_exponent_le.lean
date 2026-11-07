-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:39:46.358015+00:00
-- url     : https://prove2.me/submissions/0037ad27-2085-437e-9f7d-bca3f5723173

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_expr_ge_ell_of_large

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j : ℕ) (b : ℤ) :
    {ℓ : ℕ | -2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2) ≤ b}.Finite := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ ℓ : ℕ, N ≤ ℓ → b < -2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2) :=
    ⟨(b.toNat + 1) + (2 * j + 2), fun ℓ hℓ =>
      lt_of_lt_of_le (by omega) (expr_ge_ell_of_large j ℓ (by omega))⟩
  exact (Set.finite_lt_nat N).subset fun ℓ hℓ => by
    simp only [Set.mem_setOf_eq] at hℓ ⊢; by_contra h; push_neg at h
    exact not_lt.mpr hℓ (hN ℓ h)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
