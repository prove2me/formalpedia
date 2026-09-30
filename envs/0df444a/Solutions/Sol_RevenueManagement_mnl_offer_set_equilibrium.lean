-- Prove2me | solution 1 for RevenueManagement.mnl_offer_set_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T23:26:07.106984+00:00
-- url     : https://prove2.me/submissions/2b4e2955-c9be-4f26-91ff-1ddf3a9e67d1

import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

open Finset

lemma mnl_weight_nonneg (A : OfferFirm) (hA : A.IsModel) (k : ℕ) : 0 ≤ A.weight k :=
  sum_nonneg fun j _ => (hA.2.1 j).le

lemma mnl_den_pos (A B : OfferFirm) (w0 : ℝ) (hw0 : 0 < w0) (hA : A.IsModel)
    (hB : B.IsModel) (k l : ℕ) : 0 < A.weight k + B.weight l + w0 := by
  have := mnl_weight_nonneg A hA k
  have := mnl_weight_nonneg B hB l
  linarith

/-- The potential `g₁(k) g₂(l) / D(k, l)` factors through either firm's payoff. -/
lemma mnl_psi1 (A B : OfferFirm) (w0 : ℝ) (k l : ℕ) :
    A.g w0 k * B.g w0 l / (A.weight k + B.weight l + w0) =
      B.g w0 l * offerPayoff1 A B w0 k l := by
  unfold offerPayoff1; ring

lemma mnl_psi2 (A B : OfferFirm) (w0 : ℝ) (k l : ℕ) :
    A.g w0 k * B.g w0 l / (A.weight k + B.weight l + w0) =
      A.g w0 k * offerPayoff2 A B w0 k l := by
  unfold offerPayoff2; ring

theorem mnl_main (A B : OfferFirm) (w0 : ℝ) (hw0 : 0 < w0) (hA : A.IsModel)
    (hB : B.IsModel) (hcase : (A.CaseI w0 ∧ B.CaseI w0) ∨ (A.CaseII w0 ∧ B.CaseII w0)) :
    ∃ k l, IsOfferEquilibrium A B w0 k l := by
  have hD := mnl_den_pos A B w0 hw0 hA hB
  have hAne : (Icc 1 A.n).Nonempty := ⟨1, mem_Icc.mpr ⟨le_rfl, hA.1⟩⟩
  have hBne : (Icc 1 B.n).Nonempty := ⟨1, mem_Icc.mpr ⟨le_rfl, hB.1⟩⟩
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- Case I
    by_cases hp1 : ∃ k ∈ Icc 1 A.n, 0 < A.g w0 k
    · by_cases hp2 : ∃ l ∈ Icc 1 B.n, 0 < B.g w0 l
      · -- both firms have a set with positive `g`: maximize the potential on those sets
        obtain ⟨k1, hk1, hk1p⟩ := hp1
        obtain ⟨l1, hl1, hl1p⟩ := hp2
        have hne : (((Icc 1 A.n).filter fun k => 0 < A.g w0 k) ×ˢ
            ((Icc 1 B.n).filter fun l => 0 < B.g w0 l)).Nonempty :=
          ⟨(k1, l1), mem_product.mpr ⟨mem_filter.mpr ⟨hk1, hk1p⟩, mem_filter.mpr ⟨hl1, hl1p⟩⟩⟩
        obtain ⟨⟨k, l⟩, hkl, hmax⟩ := exists_max_image _
          (fun kl : ℕ × ℕ => A.g w0 kl.1 * B.g w0 kl.2 / (A.weight kl.1 + B.weight kl.2 + w0)) hne
        obtain ⟨hk, hl⟩ := mem_product.mp hkl
        obtain ⟨hkI, hkp⟩ := mem_filter.mp hk
        obtain ⟨hlI, hlp⟩ := mem_filter.mp hl
        refine ⟨k, l, hkI, hlI, fun k' hk' => ?_, fun l' hl' => ?_⟩
        · by_cases hk'p : 0 < A.g w0 k'
          · have := hmax (k', l) (mem_product.mpr ⟨mem_filter.mpr ⟨hk', hk'p⟩, hl⟩)
            simp only [mnl_psi1] at this
            exact le_of_mul_le_mul_left this hlp
          · have e1 : offerPayoff1 A B w0 k' l ≤ 0 :=
              div_nonpos_of_nonpos_of_nonneg (not_lt.mp hk'p) (hD k' l).le
            have e2 : 0 < offerPayoff1 A B w0 k l := div_pos hkp (hD k l)
            linarith
        · by_cases hl'p : 0 < B.g w0 l'
          · have := hmax (k, l') (mem_product.mpr ⟨hk, mem_filter.mpr ⟨hl', hl'p⟩⟩)
            simp only [mnl_psi2] at this
            exact le_of_mul_le_mul_left this hkp
          · have e1 : offerPayoff2 A B w0 k l' ≤ 0 :=
              div_nonpos_of_nonpos_of_nonneg (not_lt.mp hl'p) (hD k l').le
            have e2 : 0 < offerPayoff2 A B w0 k l := div_pos hlp (hD k l)
            linarith
      · -- firm 2's best complete set has `g = 0`: it plays it, firm 1 best-responds
        obtain ⟨l0, hl0, hl0g⟩ := h2
        have hl0z : B.g w0 l0 = 0 := le_antisymm (not_lt.mp fun h => hp2 ⟨l0, hl0, h⟩) hl0g
        obtain ⟨k, hk, hmax⟩ := exists_max_image (Icc 1 A.n)
          (fun k => offerPayoff1 A B w0 k l0) hAne
        refine ⟨k, l0, hk, hl0, fun k' hk' => hmax k' hk', fun l' hl' => ?_⟩
        have : offerPayoff2 A B w0 k l0 = 0 := by unfold offerPayoff2; rw [hl0z, zero_div]
        rw [this]
        exact div_nonpos_of_nonpos_of_nonneg (not_lt.mp fun h => hp2 ⟨l', hl', h⟩) (hD k l').le
    · -- firm 1's best complete set has `g = 0`: it plays it, firm 2 best-responds
      obtain ⟨k0, hk0, hk0g⟩ := h1
      have hk0z : A.g w0 k0 = 0 := le_antisymm (not_lt.mp fun h => hp1 ⟨k0, hk0, h⟩) hk0g
      obtain ⟨l, hl, hmax⟩ := exists_max_image (Icc 1 B.n)
        (fun l => offerPayoff2 A B w0 k0 l) hBne
      refine ⟨k0, l, hk0, hl, fun k' hk' => ?_, fun l' hl' => hmax l' hl'⟩
      have : offerPayoff1 A B w0 k0 l = 0 := by unfold offerPayoff1; rw [hk0z, zero_div]
      rw [this]
      exact div_nonpos_of_nonpos_of_nonneg (not_lt.mp fun h => hp1 ⟨k', hk', h⟩) (hD k' l).le
  · -- Case II: all `g < 0`; minimize the (positive) potential
    obtain ⟨⟨k, l⟩, hkl, hmin⟩ := exists_min_image ((Icc 1 A.n) ×ˢ (Icc 1 B.n))
      (fun kl : ℕ × ℕ => A.g w0 kl.1 * B.g w0 kl.2 / (A.weight kl.1 + B.weight kl.2 + w0))
      (hAne.product hBne)
    obtain ⟨hk, hl⟩ := mem_product.mp hkl
    refine ⟨k, l, hk, hl, fun k' hk' => ?_, fun l' hl' => ?_⟩
    · have := hmin (k', l) (mem_product.mpr ⟨hk', hl⟩)
      simp only [mnl_psi1] at this
      have hneg := h2 l hl
      nlinarith
    · have := hmin (k, l') (mem_product.mpr ⟨hk, hl'⟩)
      simp only [mnl_psi2] at this
      have hneg := h1 k hk
      nlinarith

end RevenueManagement

open RevenueManagement

theorem solution (A B : OfferFirm) (w0 : ℝ) (hw0 : 0 < w0) (hA : A.IsModel)
    (hB : B.IsModel) (hcase : (A.CaseI w0 ∧ B.CaseI w0) ∨ (A.CaseII w0 ∧ B.CaseII w0)) :
    ∃ k l, IsOfferEquilibrium A B w0 k l :=
  mnl_main A B w0 hw0 hA hB hcase
