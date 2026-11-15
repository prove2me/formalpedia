-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_4_15
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:53:52.724696+00:00
-- url     : https://prove2.me/submissions/4b113fcf-7899-4c6a-b1f1-b494b859bd34

import Mathlib
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_12
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_13

set_option autoImplicit false

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_4_15
section
open MeasureTheory Set StratifyMarkets.DoubleAuction

private theorem buyers_mono {n m : ℕ} (I : DAInstance n m) (hi : ℝ) :
    Antitone (fun q => I.expBuyersIn q hi) := by
  intro x y hxy
  apply Finset.sum_le_sum
  intro i _
  let := I.isProb_B i
  exact measureReal_mono (Icc_subset_Icc_left hxy)

private theorem sellers_mono {n m : ℕ} (I : DAInstance n m) (lo : ℝ) :
    Monotone (fun q => I.expSellersIn lo q) := by
  intro x y hxy
  apply Finset.sum_le_sum
  intro j _
  let := I.isProb_S j
  exact measureReal_mono (Icc_subset_Icc_right hxy)

private theorem low_price {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) (a b p : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hap : a ≤ p) (hpb : p ≤ b)
    (hB : I.expBuyersIn p b ≤ 1 / 4) (hS : I.expSellersIn a p ≤ 1 / 4) :
    1 / 7 * I.superFP a p b ≤ I.worstRationedIn a p b := by
  have h := lemma_4_12 I a b p ha hab hb hap hpb hB hS
  have hpos : 0 ≤ I.superFP a p b := by
    apply integral_nonneg
    intro x
    change 0 ≤ (if _ then _ else (0:ℝ))
    split_ifs with H
    · exact sub_nonneg.mpr (H.2.1.trans H.2.2.1)
    · exact le_rfl
  linarith

theorem solution {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) (a b p tB tS : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hap : a ≤ p) (hpb : p ≤ b)
    (htB : I.IsBuyerThreshold a b tB) (htS : I.IsSellerThreshold a b tS) (hlt : tB < tS) :
    ∃ p' ∈ Icc a b, 1 / 7 * I.superFP a p b ≤ I.worstRationedIn a p' b := by
  obtain ⟨buy, sell⟩ := lemma_4_13 I a b p ha hab hb hap hpb
  by_cases low : p ≤ tB
  · have B := (buyers_mono I b low)
    have S := (sellers_mono I a hlt.le)
    dsimp only at B S
    rw [htB.2] at B
    rw [htS.2] at S
    exact ⟨tB, htB.1, (buy B tB low htB.1.2 htB.2).2 S⟩
  by_cases high : tS ≤ p
  · have S := sellers_mono I a high
    have B := buyers_mono I b hlt.le
    dsimp only at B S
    rw [htB.2] at B
    rw [htS.2] at S
    exact ⟨tS, htS.1, (sell S tS htS.1.1 high htS.2).2 B⟩
  have B := buyers_mono I b (le_of_not_ge low)
  have S := sellers_mono I a (le_of_not_ge high)
  dsimp only at B S
  rw [htB.2] at B
  rw [htS.2] at S
  exact ⟨p, ⟨hap, hpb⟩, low_price I a b p ha hab hb hap hpb B S⟩
end
