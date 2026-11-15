-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:49:17.647545+00:00
-- url     : https://prove2.me/submissions/f644d934-599e-4029-bba9-ac4684a241c2

import Mathlib
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_3
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_4
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_5

set_option autoImplicit false

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_4_6
section
open MeasureTheory Set StratifyMarkets.DoubleAuction

private theorem excess_prices {n m : ℕ} (I : DAInstance n m) (pt : ℝ)
    (hpt : I.IsBalancedPrice pt) (hlam : 4 ≤ I.expB pt) :
    (∃ p, I.IsExcessSupplyPrice p) ∧ (∃ p, I.IsExcessDemandPrice p) := by
  have buyers_cont : ContinuousOn I.expB (Icc 0 1) := by
    unfold DAInstance.expB
    refine continuousOn_finsetSum _ fun i _ ↦ ?_
    let := I.isProb_B i
    let := I.noAtoms_B i
    have h : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ici 0) (I.μB i) :=
      (integrable_const 1).integrableOn
    simpa only [setIntegral_one_eq_measureReal, measureReal_def] using
      (h.continuousOn_Ici_primitive_Ici.mono (show Icc (0 : ℝ) 1 ⊆ Ici 0 from Icc_subset_Ici_self))
  have sellers_cont : ContinuousOn I.expS (Icc 0 1) := by
    unfold DAInstance.expS
    refine continuousOn_finsetSum _ fun j _ ↦ ?_
    let := I.isProb_S j
    let := I.noAtoms_S j
    have h : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Iic 1) (I.μS j) :=
      (integrable_const 1).integrableOn
    simpa only [setIntegral_one_eq_measureReal, measureReal_def] using
      (h.continuousOn_Iic_primitive_Iic.mono (show Icc (0 : ℝ) 1 ⊆ Iic 1 from Icc_subset_Iic_self))
  have buyers_at_one : I.expB 1 = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    let := I.isProb_B i
    let := I.noAtoms_B i
    have h := (prob_compl_eq_zero_iff measurableSet_Icc).2 (I.support_B i)
    have ho : I.μB i (Ioi 1) = 0 :=
      measure_mono_null (t := (Icc (0 : ℝ) 1)ᶜ) (fun _ hx hmem ↦ (not_lt_of_ge hmem.2) hx) h
    rw [← measure_congr Ioi_ae_eq_Ici, ho, ENNReal.toReal_zero]
  have sellers_at_zero : I.expS 0 = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    let := I.isProb_S j
    let := I.noAtoms_S j
    have h := (prob_compl_eq_zero_iff measurableSet_Icc).2 (I.support_S j)
    have ho : I.μS j (Iio 0) = 0 :=
      measure_mono_null (t := (Icc (0 : ℝ) 1)ᶜ) (fun _ hx hmem ↦ (not_lt_of_ge hmem.1) hx) h
    rw [← measure_congr Iio_ae_eq_Iic, ho, ENNReal.toReal_zero]
  have hB : I.expB pt ≤ I.expB 0 := by
    apply Finset.sum_le_sum
    intro i _
    let := I.isProb_B i
    exact measureReal_mono (Ici_subset_Ici.mpr hpt.1.1)
  have hS : I.expS pt ≤ I.expS 1 := by
    apply Finset.sum_le_sum
    intro i _
    let := I.isProb_S i
    exact measureReal_mono (Iic_subset_Iic.mpr hpt.1.2)
  have H₀ : I.expS 0 - I.expB 0 ≤ -2 := by rw [sellers_at_zero]; linarith
  have H₁ : 2 ≤ I.expS 1 - I.expB 1 := by rw [buyers_at_one]; linarith [hpt.2]
  have value (c : ℝ) (hl : -2 ≤ c) (hu : c ≤ 2) :
      ∃ p ∈ Icc (0 : ℝ) 1, I.expS p - I.expB p = c :=
    isPreconnected_Icc.intermediate_value (left_mem_Icc.mpr zero_le_one)
      (right_mem_Icc.mpr zero_le_one) (sellers_cont.sub buyers_cont) ⟨H₀.trans hl, hu.trans H₁⟩
  obtain ⟨b, hb, hbal⟩ := value 2 (by norm_num) (by norm_num)
  obtain ⟨a, ha, hal⟩ := value (-2) (by norm_num) (by norm_num)
  exact ⟨⟨b, hb, hbal⟩, ⟨a, ha, by linarith⟩⟩

theorem solution {n m : ℕ} (I : DAInstance n m) (pt : ℝ)
    (hpt : I.IsBalancedPrice pt) (hlam : 4 ≤ I.expB pt) :
    ∃ p ∈ Icc (0 : ℝ) 1, 1 / 40 * I.FB ≤ I.worstRationed p := by
  obtain ⟨⟨b, hb⟩, ⟨a, ha⟩⟩ := excess_prices I pt hpt hlam
  have hfb := lemma_4_3 I pt b a hpt hlam hb ha
  obtain ⟨hbuy, hsell⟩ := lemma_4_4 I pt b a hpt hlam hb ha
  have hgap := lemma_4_5 I pt b a hpt hlam hb ha
  have hmid : (b+a)/2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hb.1.1, ha.1.1], by linarith [hb.1.2, ha.1.2]⟩
  by_contra! h
  have h₁ := h b hb.1
  have h₂ := h a ha.1
  have h₃ := h _ hmid
  linarith
end
