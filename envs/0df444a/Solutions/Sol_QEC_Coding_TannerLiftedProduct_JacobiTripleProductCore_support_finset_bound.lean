-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.support_finset_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:49:58.518983+00:00
-- url     : https://prove2.me/submissions/d10e684f-9f5b-4c30-b7c1-1afbba85cbd1

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (d : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)), ∀ (k ℓ : ℕ),
      ((k + ℓ) ^ 2 + ℓ : ℕ) ≤ d → (k, ℓ) ∈ S :=
  ⟨Finset.range (d + 1) ×ˢ Finset.range (d + 1), fun k ℓ h => by
    simp only [Finset.mem_product, Finset.mem_range]
    constructor <;> nlinarith [Nat.zero_le k, Nat.zero_le ℓ]⟩
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
