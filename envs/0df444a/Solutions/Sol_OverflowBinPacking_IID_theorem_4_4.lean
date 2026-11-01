-- Prove2me | solution 1 for OverflowBinPacking.IID.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:23:27.966198+00:00
-- url     : https://prove2.me/submissions/5b8af275-0ae5-4523-9b67-cdc56ff95104

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_BudgetedGreedy
import Theorems.Thm_OverflowBinPacking_IID_budgeted_greedy_policy
import Theorems.Thm_OverflowBinPacking_IID_heavy_case
import Theorems.Thm_OverflowBinPacking_IID_corollary_3_5
import Theorems.Thm_OverflowBinPacking_IID_theorem_4_1
import Theorems.Thm_OverflowBinPacking_IID_lemma_4_3

open MeasureTheory OverflowBinPacking.IID

lemma obp_red_measurable_usage {n : ℕ} (a : Rule n) (ha : MeasurableRule a)
    (j : Fin n) (t : ℕ) : Measurable (fun x => usage a x j t) := by
  classical
  unfold usage
  simp_rw [Finset.sum_filter]
  refine Finset.measurable_sum _ (fun k _ => ?_)
  refine Measurable.ite ?_ (measurable_pi_apply k) measurable_const
  by_cases hk : (k : ℕ) < t
  · simpa [hk] using ha k j
  · simp [hk]

lemma obp_red_measurable_opened {n : ℕ} (a : Rule n) (ha : MeasurableRule a) :
    Measurable (fun x => (numOpened a x : ℝ)) := by
  classical
  have h1 : Measurable (fun x : Fin n → ℝ => (fun i => a i x)) := by
    refine measurable_pi_iff.mpr (fun i => ?_)
    refine measurable_to_countable' (fun j => ?_)
    exact ha i j
  have h2 : Measurable (fun f : Fin n → Fin n => ((Finset.univ.image f).card : ℝ)) :=
    measurable_of_countable _
  exact h2.comp h1

lemma obp_red_measurable_broken {n : ℕ} (a : Rule n) (ha : MeasurableRule a) :
    Measurable (fun x => (numBroken a x : ℝ)) := by
  classical
  have : (fun x => (numBroken a x : ℝ)) =
      fun x => ∑ j : Fin n, (if 1 < usage a x j n then (1 : ℝ) else 0) := by
    funext x
    rw [numBroken, Finset.card_filter]
    push_cast
    rfl
  rw [this]
  refine Finset.measurable_sum _ (fun j _ => ?_)
  exact Measurable.ite (measurableSet_lt measurable_const
    (obp_red_measurable_usage a ha j n)) measurable_const measurable_const

lemma obp_red_opened_le_cost {n : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (C : ℝ) (hC : 0 ≤ C) (a : Rule n) (ha : IsPolicy a) :
    (∫ x, (numOpened a x : ℝ) ∂(Measure.pi (fun _ : Fin n => ν))) ≤
      cost (fun _ : Fin n => ν) C a := by
  unfold cost
  have hm1 := obp_red_measurable_opened a ha.2.1
  have hm2 := obp_red_measurable_broken a ha.2.1
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => by positivity)) ?_
    (Filter.Eventually.of_forall (fun x => ?_))
  · refine Integrable.of_bound (hm1.add (hm2.const_mul C)).aestronglyMeasurable
      ((n : ℝ) + C * n) (Filter.Eventually.of_forall (fun x => ?_))
    have hO : (numOpened a x : ℝ) ≤ n := by
      have : numOpened a x ≤ n := by
        unfold numOpened
        calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
          _ = n := by simp
      exact_mod_cast this
    have hB : (numBroken a x : ℝ) ≤ n := by
      have : numBroken a x ≤ n := by
        unfold numBroken
        calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
          _ = n := by simp
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ numOpened a x + C * numBroken a x := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    have := mul_le_mul_of_nonneg_left hB hC
    linarith
  · have : (0 : ℝ) ≤ C * numBroken a x := by positivity
    simp only
    linarith

theorem solution (n : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν0 : ν (Set.Iio 0) = 0) :
    IsPolicy (bgRule (fun _ : Fin n => ν) C (Real.sqrt 2)) ∧
    ∀ a : Rule n, IsPolicy a →
      cost (fun _ : Fin n => ν) C
        (bgRule (fun _ : Fin n => ν) C (Real.sqrt 2)) ≤
      (3 + 2 * Real.sqrt 2) * cost (fun _ : Fin n => ν) C a := by
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hCpos : 0 < C := by linarith
  refine ⟨budgeted_greedy_policy (fun _ : Fin n => ν) (fun _ => inferInstance)
    (fun _ => hν0) C (Real.sqrt 2) hC hs2, ?_⟩
  intro a ha
  by_cases hH : Real.sqrt 2 / C < ν.real (Set.Ioi 1)
  · -- heavy-item case
    obtain ⟨hAlg, hOpt⟩ := heavy_case (n := n) ν hν0 C hC hH
    have hOa := hOpt a ha
    rw [hAlg]
    have hp : 0 ≤ ν.real (Set.Ioi 1) := measureReal_nonneg
    have hCp : Real.sqrt 2 < C * ν.real (Set.Ioi 1) := by
      rw [div_lt_iff₀ hCpos] at hH; linarith
    have hn : (0 : ℝ) ≤ n := by positivity
    have key : (n : ℝ) * (1 + C * ν.real (Set.Ioi 1)) ≤
        (3 + 2 * Real.sqrt 2) * ((n : ℝ) * C * ν.real (Set.Ioi 1)) := by
      have h1 : 1 + C * ν.real (Set.Ioi 1) ≤
          (3 + 2 * Real.sqrt 2) * (C * ν.real (Set.Ioi 1)) := by nlinarith
      have := mul_le_mul_of_nonneg_left h1 hn
      linarith
    exact key.trans (mul_le_mul_of_nonneg_left hOa (by positivity))
  · -- light case
    push Not at hH
    obtain ⟨a', ha', hIso, hcost'⟩ :=
      theorem_4_1 (fun _ : Fin n => ν) (fun _ => inferInstance) (fun _ => hν0) C (Real.sqrt 2)
        hC (by positivity) a ha
    have hBud : IsBudgeted (fun _ : Fin n => ν) a' (Real.sqrt 2 / C) := by
      intro x j
      exact hIso.2 x j (fun _ _ => hH)
    have h35 := corollary_3_5 (fun _ : Fin n => ν) (fun _ => inferInstance) (fun _ => hν0) C
      (Real.sqrt 2) hC hs2 (fun _ => hH)
    have h43 := (lemma_4_3 (n := n) ν hν0 C (Real.sqrt 2) hC hs2 hH).2 a' ha' hBud
    have hN := obp_red_opened_le_cost ν C hCpos.le a' ha'
    have h2 : 1 + 2 / Real.sqrt 2 = 1 + Real.sqrt 2 := by
      field_simp
      nlinarith
    rw [h2] at hcost'
    have e : (3 + 2 * Real.sqrt 2) = (1 + Real.sqrt 2) * (1 + Real.sqrt 2) := by nlinarith
    rw [e, mul_assoc]
    refine h35.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact h43.trans (hN.trans hcost')
