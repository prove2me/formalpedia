-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.theorem_D_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:11.69233+00:00
-- url     : https://prove2.me/submissions/07588157-90fc-4c60-af79-fc6a5fe3f30d

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution : LinearPurityFails := by
  open TradingPostNSW.Leontief MeasureTheory in
  focus
    classical
    let I := linearRefutationInstance
    let b : ℝ → Fin 3 → Fin 2 → ℝ := fun t i j =>
      if i = 0 then (if j = 0 then t else 1-t) else (if j = 0 then 0 else 1)
    have hb (t : ℝ) (ht : t = 1 ∨ t = 1/2) (i : Fin 3) : Strategy I i (b t i) := by
      rcases ht with rfl | rfl <;> fin_cases i <;>
        norm_num [Strategy, I, linearRefutationInstance, b, Fin.forall_fin_two, Fin.sum_univ_two]
    have ha (s : Fin 3 → Fin 2 → ℝ) (hs : ∀ i j, 0 ≤ s i j) (i : Fin 3) (j : Fin 2) :
        tpAlloc 0 s i j = s i j / ∑ k, s k j := by
      simp only [tpAlloc, effBid, if_pos (hs i j)]
      have he : (fun k => if 0 ≤ s k j then s k j else 0) = fun k => s k j := by
        funext k
        exact if_pos (hs k j)
      simp only [he]
      split_ifs with h
      · rfl
      · rw [show s i j = 0 by linarith [hs i j], zero_div]
    have hpay (t : ℝ) (ht : t = 1 ∨ t = 1/2) (i : Fin 3)
        (r : Fin 2 → ℝ) (hr : Strategy I i r) :
        linU I i (tpAlloc 0 (Function.update (b t) i r) i) ≤ linU I i (tpAlloc 0 (b t) i) := by
      have hnn : ∀ k j, 0 ≤ b t k j := fun k j => (hb t ht k).1 j |>.1
      have hnu : ∀ k j, 0 ≤ Function.update (b t) i r k j := by
        intro k j
        by_cases h : k = i
        · subst k; simpa using (hr.1 j).1
        · simpa [Function.update_of_ne h] using hnn k j
      have hr0 := (hr.1 0).1
      have hr1 := (hr.1 1).1
      have hrS : r 0 + r 1 = 1 := by
        simpa [Strategy, Fin.sum_univ_two, I, linearRefutationInstance] using hr.2
      simp only [linU, Fin.sum_univ_two, ha _ hnn, ha _ hnu]
      rcases ht with rfl | rfl <;> fin_cases i <;>
        norm_num [I, linearRefutationInstance, b, Fin.sum_univ_succ, Function.update, Fin.succ]
      · exact div_self_le_one _
      · have hd0 : 0 < 1 + r 0 := by linarith
        have hd1 : 0 < r 1 + 1 := by linarith
        apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).2
        field_simp
        nlinarith [sq_nonneg (r 0)]
      · apply (div_le_iff₀ (by linarith : 0 < 1 + r 1)).2
        linarith
      · exact div_self_le_one _
      · have hd0 : 0 < 1/2 + r 0 := by linarith
        have hd1 : 0 < 1/2 + (r 1 + 1) := by linarith
        field_simp
        nlinarith [sq_nonneg (r 0)]
      · apply (div_le_iff₀ (by linarith : 0 < 1/2 + (1 + r 1))).2
        linarith
    let q : ENNReal := 1/2
    have hq : q ≠ ⊤ := by norm_num [q]
    have hqq : q + q = 1 := ENNReal.add_halves 1
    let mix : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ProbabilityMeasure (Fin 2 → ℝ) :=
      fun a c => ⟨q • Measure.dirac a + q • Measure.dirac c, by
        constructor
        simp [Measure.add_apply, Measure.smul_apply, hqq]⟩
    have hpi (τ : Fin 3 → ProbabilityMeasure (Fin 2 → ℝ))
        (a c : Fin 3 → Fin 2 → ℝ)
        (h0 : (τ 0 : Measure (Fin 2 → ℝ)) = q • Measure.dirac (a 0) + q • Measure.dirac (c 0))
        (h1 : (τ 1 : Measure (Fin 2 → ℝ)) = Measure.dirac (a 1))
        (h2 : (τ 2 : Measure (Fin 2 → ℝ)) = Measure.dirac (a 2))
        (he1 : c 1 = a 1) (he2 : c 2 = a 2) :
        joint τ = q • Measure.dirac a + q • Measure.dirac c := by
      unfold joint
      apply Measure.pi_eq
      intro s hs
      rw [Fin.prod_univ_three, h0, h1, h2]
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      by_cases hA : a 0 ∈ s 0 <;> by_cases hC : c 0 ∈ s 0 <;>
        by_cases hB : a 1 ∈ s 1 <;> by_cases hD : a 2 ∈ s 2 <;>
        simp [Measure.dirac_apply, Set.mem_pi, Fin.forall_fin_succ, Fin.succ,
          he1, he2, hA, hC, hB, hD]
    let σ : Fin 3 → ProbabilityMeasure (Fin 2 → ℝ) := fun i =>
      if i = 0 then mix (b 1 0) (b (1/2) 0) else pureBid (b 1 i)
    have hj : joint σ = q • Measure.dirac (b 1) + q • Measure.dirac (b (1/2)) := by
      apply hpi <;> simp [σ, mix, pureBid, b]
    have hd (i : Fin 3) (r : Fin 2 → ℝ) :
        joint (Function.update σ i (pureBid r)) =
          q • Measure.dirac (Function.update (b 1) i r) +
          q • Measure.dirac (Function.update (b (1/2)) i r) := by
      fin_cases i <;> apply hpi <;>
        simp [σ, pureBid, mix, Function.update, b, ← add_smul, hqq]
    have hint (a c : Fin 3 → Fin 2 → ℝ) (f : (Fin 3 → Fin 2 → ℝ) → ℝ) :
        Integrable f (q • Measure.dirac a + q • Measure.dirac c) := by
      exact ((integrable_dirac (by simp)).smul_measure hq).add_measure
        ((integrable_dirac (by simp)).smul_measure hq)
    have h_int (a c : Fin 3 → Fin 2 → ℝ) (f : (Fin 3 → Fin 2 → ℝ) → ℝ) :
        (∫ s, f s ∂(q • Measure.dirac a + q • Measure.dirac c)) =
        q.toReal * f a + q.toReal * f c := by
      rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure hq)
        ((integrable_dirac (by simp)).smul_measure hq)]
      simp [integral_smul_measure]
    change LinStanding I ∧ PerfectCompetition I ∧ (∀ i, ∃ j, 0 < I.v i j) ∧ _
    refine ⟨?_, ?_, ?_, σ, ?_, ?_⟩
    · constructor
      · norm_num
      · intro i j; fin_cases i <;> fin_cases j <;> norm_num [I, linearRefutationInstance]
      · intro i; norm_num [I, linearRefutationInstance]
    · intro j; fin_cases j
      · exact ⟨0, 1, by decide, by norm_num [I, linearRefutationInstance],
          by norm_num [I, linearRefutationInstance]⟩
      · exact ⟨1, 2, by decide, by norm_num [I, linearRefutationInstance],
          by norm_num [I, linearRefutationInstance, show (2 : Fin 3) ≠ 0 by decide]⟩
    · intro i; fin_cases i
      · exact ⟨0, by norm_num [I, linearRefutationInstance]⟩
      · exact ⟨1, by norm_num [I, linearRefutationInstance]⟩
      · exact ⟨1, by norm_num [I, linearRefutationInstance]⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro i
        by_cases hi : i = 0
        · subst i
          change ∀ᵐ r ∂(q • Measure.dirac (b 1 0) + q • Measure.dirac (b (1/2) 0)), Strategy I 0 r
          rw [ae_add_measure_iff]
          constructor
          · apply Measure.ae_smul_measure
            simpa only [ae_dirac_eq, Filter.eventually_pure] using hb 1 (Or.inl rfl) 0
          · apply Measure.ae_smul_measure
            simpa only [ae_dirac_eq, Filter.eventually_pure] using hb (1/2) (Or.inr rfl) 0
        · have hσ : σ i = pureBid (b 1 i) := if_neg hi
          rw [hσ]
          change ∀ᵐ r ∂Measure.dirac (b 1 i), Strategy I i r
          simpa only [ae_dirac_eq, Filter.eventually_pure] using hb 1 (Or.inl rfl) i
      · intro i
        rw [hj]
        exact hint _ _ _
      · intro i r hr
        constructor
        · rw [hd]
          exact hint _ _ _
        · unfold expPay
          rw [hd, hj, h_int, h_int]
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hpay 1 (Or.inl rfl) i r hr) ENNReal.toReal_nonneg)
            (mul_le_mul_of_nonneg_left (hpay (1/2) (Or.inr rfl) i r hr) ENNReal.toReal_nonneg)
    · intro hp
      obtain ⟨r, hr⟩ := hp 0
      have hne : b (1/2) 0 ≠ b 1 0 := by
        intro h
        have := congrFun h 0
        norm_num [b] at this
      have hm : (σ 0 : Measure (Fin 2 → ℝ)) {b 1 0} = q := by
        change (q • Measure.dirac (b 1 0) + q • Measure.dirac (b (1/2) 0)) {b 1 0} = q
        simp only [Measure.add_apply,
          Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator_apply,
          Set.mem_singleton_iff, if_true, if_neg hne, Pi.one_apply,
          mul_one, mul_zero, add_zero]
      have he := congrArg (fun μ : ProbabilityMeasure (Fin 2 → ℝ) =>
        (μ : Measure (Fin 2 → ℝ)) {b 1 0}) hr
      rw [hm] at he
      have he' := congrArg ENNReal.toReal he
      by_cases h : r = b 1 0 <;>
        norm_num [pureBid, Measure.dirac_apply, h, q] at he'
