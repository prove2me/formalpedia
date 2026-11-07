-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegerThreeSquare_card_le_ninetySix_mul_seventh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:04:29.725504+00:00
-- url     : https://prove2.me/submissions/7e6bd5cb-37f8-456e-85ff-514b7daf1619

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatThreeSquare_card_le_twelve_mul_seventh
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerThreeSquareAbs_fiber_card_le_eight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (s : Finset ((ℤ × ℤ) × ℤ)) (n K : ℕ) (hK : 0 < K) (hn : n ≤ K^8)
    (hs : ∀ a ∈ s, a.1.1^2+a.1.2^2+a.2^2=(n : ℤ)) : s.card ≤ 96*K^7 := by
  classical
  have hNat : ∀ a ∈ s.image lpsIntegerThreeSquareAbs, a.1.1^2+a.1.2^2+a.2^2=n := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    have hh : (b.1.1.natAbs : ℤ)^2+(b.1.2.natAbs : ℤ)^2+(b.2.natAbs : ℤ)^2=(n : ℤ) := by
      simpa only [Int.natCast_natAbs, sq_abs] using hs b hb
    change b.1.1.natAbs^2+b.1.2.natAbs^2+b.2.natAbs^2=n
    exact_mod_cast hh
  have hcount := lpsNatThreeSquare_card_le_twelve_mul_seventh (s.image lpsIntegerThreeSquareAbs) n K hK hn hNat
  have hc := Finset.card_le_mul_card_image s 8 (fun a _ => lpsIntegerThreeSquareAbs_fiber_card_le_eight s a)
  calc
    s.card ≤ 8*(s.image lpsIntegerThreeSquareAbs).card := hc
    _ ≤ 8*(12*K^7) := Nat.mul_le_mul_left _ hcount
    _ = 96*K^7 := by ring
end QEC.Coding.TannerLiftedProduct
