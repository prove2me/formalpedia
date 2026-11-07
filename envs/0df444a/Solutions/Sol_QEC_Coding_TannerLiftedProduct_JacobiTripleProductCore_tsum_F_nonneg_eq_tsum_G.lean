-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_F_nonneg_eq_tsum_G
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:40:08.517741+00:00
-- url     : https://prove2.me/submissions/72d3a8bc-b009-4ab8-b436-0ed4a727a6ee

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    (∑' (p : {p : ℤ × ℕ // 0 ≤ p.1}), F p.val) =
    (∑' (p : ℕ × ℕ), G p) := by
  letI := piTop
  have : (∑' (p : {p : ℤ × ℕ // 0 ≤ p.1}), F p.val) =
         (∑' (p : ℕ × ℕ), F ((↑p.1 : ℤ), p.2)) := by
    let e : ℕ × ℕ ≃ {p : ℤ × ℕ // 0 ≤ p.1} :=
      { toFun := fun p => ⟨(↑p.1, p.2), Int.natCast_nonneg p.1⟩
        invFun := fun p => (p.1.1.toNat, p.1.2)
        left_inv := fun p => by simp [Int.toNat_natCast]
        right_inv := fun ⟨⟨z, n⟩, hz⟩ => by
          simp only
          exact Subtype.ext (Prod.ext (by simp [Int.toNat_of_nonneg hz]) rfl) }
    rw [← Equiv.tsum_eq e]; congr 1
  rw [this]
  exact tsum_congr fun ⟨k, ℓ⟩ => by simp only [F, G, show (↑k + ↑ℓ : ℤ).natAbs = k + ℓ by omega]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
