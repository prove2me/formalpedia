-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.support_finset_Z_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:40:01.071506+00:00
-- url     : https://prove2.me/submissions/71b10eac-ff2d-492b-a467-ad2d8b715b90

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
set_option maxHeartbeats 800000
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (d : ℕ) :
    ∃ (S_fin : Finset (ℤ × ℕ)), ∀ (z : ℤ) (ℓ : ℕ),
      (z + ↑ℓ).natAbs ^ 2 + ℓ ≤ d → (z, ℓ) ∈ S_fin := by
  use (Finset.Icc (-2 * (d : ℤ)) (d : ℤ)) ×ˢ (Finset.Icc 0 d)
  intro z ℓ h
  have h₁ : ℓ ≤ d := by nlinarith
  have h₂ : (z + ℓ).natAbs ≤ d := by nlinarith
  have h₃ : (z : ℤ) ≥ -2 * (d : ℤ) := by
    have h₅ : -(z + ↑ℓ) ≤ ↑(z + ↑ℓ).natAbs := by
      rw [← Int.natAbs_neg]
      exact Int.le_natAbs
    linarith [Int.ofNat_le.mpr h₁, Int.ofNat_le.mpr h₂]
  have h₄ : (z : ℤ) ≤ (d : ℤ) := by
    have := Int.le_natAbs (a := z + ↑ℓ)
    nlinarith [Int.ofNat_le.mpr h₂]
  simp_all
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
