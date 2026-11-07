-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.expr_ge_ell_of_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:38:13.827097+00:00
-- url     : https://prove2.me/submissions/49812fed-828e-400a-bdc5-c66ae7e09aa9

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j ℓ : ℕ) (hℓ : 2 * j + 2 ≤ ℓ) :
    (ℓ : ℤ) ≤ -2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2) := by
  have hge : 1 ≤ ℓ := by omega
  have hdvd : 2 ∣ ℓ * (ℓ - 1) := by
    rcases Nat.even_or_odd ℓ with ⟨k, hk⟩ | ⟨k, hk⟩ <;> simp [hk] <;> ring_nf <;> omega
  have h₂ : 2 * ℓ.choose 2 = ℓ * (ℓ - 1) := by
    have := Nat.choose_two_right ℓ
    omega
  zify [hge] at h₂
  nlinarith
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
