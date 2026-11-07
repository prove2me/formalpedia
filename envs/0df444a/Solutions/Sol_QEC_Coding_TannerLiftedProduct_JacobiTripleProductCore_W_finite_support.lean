-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.W_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:44:27.469119+00:00
-- url     : https://prove2.me/submissions/f9942ab4-8b19-4f68-b6ca-409f30521bb3

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_V_coeff_neg_eq_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finite_exponent_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_W_term_coeff_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j : ℕ) (b : ℤ) :
    (Function.support (fun ℓ : ℕ ↦ ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b)).Finite :=
  (finite_exponent_le j b).subset fun ℓ hℓ => by
    simp only [Function.mem_support, ne_eq, Set.mem_setOf_eq] at hℓ ⊢; by_contra h; push_neg at h
    exact hℓ (by rw [W_term_coeff_eq, V_coeff_neg_eq_zero ℓ _ (by
      have : (ℓ.choose 2 : ℤ) ≤ ↑(ℓ + ℓ.choose 2) := by exact_mod_cast Nat.le_add_left _ _
      linarith), mul_zero])
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
