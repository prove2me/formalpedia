-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_4_14
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:53:51.832728+00:00
-- url     : https://prove2.me/submissions/92ae6846-b814-4b9e-b6d3-d98ee7c3b5b7

import Mathlib
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_12
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_13

set_option autoImplicit false

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_4_14
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

private theorem buyer_threshold {n m : ℕ} (I : DAInstance n m) {p b : ℝ} (hp : p ≤ b)
    (h : 1 / 4 ≤ I.expBuyersIn p b) : ∃ t ∈ Icc p b, I.expBuyersIn t b = 1 / 4 := by
  have hc : ContinuousOn (fun t => I.expBuyersIn t b) (Icc p b) := by
    apply continuousOn_finsetSum
    intro i _
    let := I.isProb_B i
    let := I.noAtoms_B i
    let μ := (I.μB i).restrict (Iic b)
    have H : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici p) μ := (integrable_const 1).integrableOn
    simpa [μ, setIntegral_one_eq_measureReal, measureReal_def, Measure.restrict_apply,
      Ici_inter_Iic] using (H.continuousOn_Ici_primitive_Ici.mono Icc_subset_Ici_self)
  have hz : I.expBuyersIn b b = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    let := I.noAtoms_B i
    simp
  apply isPreconnected_Icc.intermediate_value (right_mem_Icc.mpr hp) (left_mem_Icc.mpr hp) hc
  exact ⟨by simp [hz], h⟩

private theorem seller_threshold {n m : ℕ} (I : DAInstance n m) {a p : ℝ} (hp : a ≤ p)
    (h : 1 / 4 ≤ I.expSellersIn a p) : ∃ t ∈ Icc a p, I.expSellersIn a t = 1 / 4 := by
  have hc : ContinuousOn (fun t => I.expSellersIn a t) (Icc a p) := by
    apply continuousOn_finsetSum
    intro j _
    let := I.isProb_S j
    let := I.noAtoms_S j
    have H : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc a p) (I.μS j) :=
      (integrable_const 1).integrableOn
    simpa [setIntegral_one_eq_measureReal, measureReal_def] using
      intervalIntegral.continuousOn_primitive_Icc H
  have hz : I.expSellersIn a a = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    let := I.noAtoms_S j
    simp
  apply isPreconnected_Icc.intermediate_value (left_mem_Icc.mpr hp) (right_mem_Icc.mpr hp) hc
  exact ⟨by simp [hz], h⟩

theorem solution {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) (a b p : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hap : a ≤ p) (hpb : p ≤ b)
    (hlow : I.expBuyersIn a b ≤ 1 / 4 ∨ I.expSellersIn a b ≤ 1 / 4) :
    ∃ p' ∈ Icc a b, 1 / 7 * I.superFP a p b ≤ I.worstRationedIn a p' b := by
  obtain ⟨buy, sell⟩ := lemma_4_13 I a b p ha hab hb hap hpb
  rcases hlow with B | S
  · by_cases h : I.expSellersIn a p ≤ 1/4
    · exact ⟨p, ⟨hap,hpb⟩, low_price I a b p ha hab hb hap hpb ((buyers_mono I b hap).trans B) h⟩
    obtain ⟨t, ht, ht'⟩ := seller_threshold I hap (le_of_not_ge h)
    exact ⟨t, ⟨ht.1, ht.2.trans hpb⟩, (sell (le_of_not_ge h) t ht.1 ht.2 ht').2
      ((buyers_mono I b ht.1).trans B)⟩
  · by_cases h : I.expBuyersIn p b ≤ 1/4
    · exact ⟨p, ⟨hap,hpb⟩, low_price I a b p ha hab hb hap hpb h ((sellers_mono I a hpb).trans S)⟩
    obtain ⟨t, ht, ht'⟩ := buyer_threshold I hpb (le_of_not_ge h)
    exact ⟨t, ⟨hap.trans ht.1, ht.2⟩, (buy (le_of_not_ge h) t ht.1 ht.2 ht').2
      ((sellers_mono I a ht.2).trans S)⟩
end
