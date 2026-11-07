-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsNatThreeSquare_card_le_twelve_mul_seventh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:03:29.274015+00:00
-- url     : https://prove2.me/submissions/dfb313d9-b847-40a2-af83-023bb7ce9117

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatSquare_coordinate_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircle_card_le_six_mul_cube
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (s : Finset ((ℕ × ℕ) × ℕ)) (n K : ℕ) (hK : 0 < K) (hn : n ≤ K^8)
    (hs : ∀ a ∈ s, a.1.1^2+a.1.2^2+a.2^2=n) : s.card ≤ 12*K^7 := by
  classical
  have hnR : n ≤ (K^4)^2 := by simpa only [← pow_mul] using hn
  have hmap : ∀ a ∈ s, a.2 ∈ Finset.range (K^4+1) := by
    intro a ha
    have hc := lpsNatSquare_coordinate_bound a.2 n (K^4) (by have := hs a ha; omega) hnR
    exact Finset.mem_range.mpr (by omega)
  have hfib : ∀ j ∈ Finset.range (K^4+1), (s.filter fun a => a.2=j).card ≤ 6*K^3 := by
    intro j _hj
    let t := s.filter fun a => a.2=j
    have hi : (t : Set ((ℕ × ℕ) × ℕ)).InjOn Prod.fst := by
      intro a ha b hb h
      have ha2 := (Finset.mem_filter.mp ha).2
      have hb2 := (Finset.mem_filter.mp hb).2
      exact Prod.ext h (ha2.trans hb2.symm)
    have he : t.card=(t.image Prod.fst).card := (Finset.card_image_of_injOn hi).symm
    rw [he]
    apply lpsNatCircle_card_le_six_mul_cube _ (n-j^2) K hK ((Nat.sub_le _ _).trans hn)
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hbS,hbj⟩ := Finset.mem_filter.mp hb
    have hbN := hs b hbS
    rw [hbj] at hbN
    omega
  have hc := Finset.card_le_mul_card_image_of_maps_to hmap (6*K^3) hfib
  have hk4 : 1 ≤ K^4 := by have := pow_pos hK 4; omega
  calc
    s.card ≤ 6*K^3*(K^4+1) := by simpa using hc
    _ ≤ 6*K^3*(2*K^4) := Nat.mul_le_mul_left _ (by omega)
    _ = 12*K^7 := by ring
end QEC.Coding.TannerLiftedProduct
