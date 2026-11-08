-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsNatCircle_card_le_fifty_mul_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:06:39.846868+00:00
-- url     : https://prove2.me/submissions/4974978b-ee35-4598-9964-307ab787f3b8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
import Mathlib.Data.Nat.Find
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAdaptiveThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircle_exists_adaptive_box_scale
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircle_card_le_boxes
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircle_card_le_coordinate_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircle_coordinates_bound


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (s : Finset (ℕ × ℕ)) (n K : ℕ)
    (hK : 0 < K) (hn : n ≤ K^6) (hs : ∀ a ∈ s, a.1^2+a.2^2=n) :
    s.card ≤ 50*K^2 := by
  have hk2 : 1 ≤ K^2 := by have := pow_pos hK 2; omega
  by_cases hsmall : n ≤ 2
  · have hc := lpsNatCircle_card_le_coordinate_bound s n 2 hs
      (fun a ha => (lpsNatCircle_coordinates_bound a n 2 (hs a ha) (by omega)).1)
    omega
  · obtain ⟨L,hL,hthin,hbound⟩ := lpsNatCircle_exists_adaptive_box_scale n (by omega)
    have hLK : L ≤ K := (Nat.pow_le_pow_iff_left (by decide : 6 ≠ 0)).mp (by omega : L^6 ≤ K^6)
    have hnR : n ≤ (12*L^3)^2 := by
      calc
        n ≤ 128*L^6 := hbound
        _ ≤ 144*L^6 := by omega
        _ = (12*L^3)^2 := by ring
    have hdiv : (12*L^3)/L=12*L^2 := by
      rw [show 12*L^3=(12*L^2)*L by ring,Nat.mul_div_cancel _ hL]
    have hL2K2 : L^2 ≤ K^2 := by gcongr
    have hB : ∀ a ∈ s, a.1/L ≤ 12*K^2 ∧ a.2/L ≤ 12*K^2 := by
      intro a ha
      have hb := lpsNatCircle_coordinates_bound a n (12*L^3) (hs a ha) hnR
      constructor
      · have hh : a.1/L ≤ (12*L^3)/L := Nat.div_le_div_right hb.1
        rw [hdiv] at hh
        exact hh.trans (Nat.mul_le_mul_left _ hL2K2)
      · have hh : a.2/L ≤ (12*L^3)/L := Nat.div_le_div_right hb.2
        rw [hdiv] at hh
        exact hh.trans (Nat.mul_le_mul_left _ hL2K2)
    have hc := lpsNatCircle_card_le_boxes s n (12*K^2) L hL hthin hs hB
    omega
end QEC.Coding.TannerLiftedProduct
