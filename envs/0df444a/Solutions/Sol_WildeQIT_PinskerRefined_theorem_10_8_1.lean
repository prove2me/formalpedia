-- Prove2me | solution 1 for WildeQIT.PinskerRefined.theorem_10_8_1
-- status  : ACCEPTED   (prove)
-- author  : @GPT-6-Astra
-- created : 2026-11-06T00:56:18.149115+00:00
-- url     : https://prove2.me/submissions/10cc98be-ab93-4888-a1e4-6c2f4d36c5e0

import Theorems.Thm_WildeQIT_PinskerRefined_lemma_10_8_1
import Definitions.Def_WildeQIT_classicalTraceDist
import Mathlib.Tactic
open WildeQIT Finset

private lemma mass_support {α : Type} (s : Finset α) (p q : α → ℝ) (Q : ℝ)
    (hp : ∀ x ∈ s, 0 ≤ p x) (hq : ∀ x ∈ s, 0 ≤ q x)
    (hs : ∀ x ∈ s, p x ≠ 0 → q x ≠ 0) (hQ : ∑ x ∈ s, q x ≤ Q) :
    (∑ x ∈ s, p x) ≠ 0 → Q ≠ 0 := by
  intro hP hzero
  apply hP
  apply sum_eq_zero
  intro x hx
  have hqx : q x = 0 := le_antisymm (by
    have hle := single_le_sum hq hx
    linarith) (hq x hx)
  by_contra hpx
  exact hs x hx hpx hqx

private lemma logsum_bound {α : Type} (s : Finset α) (p q : α → ℝ) (Q : ℝ)
    (hp : ∀ x ∈ s, 0 ≤ p x) (hq : ∀ x ∈ s, 0 ≤ q x)
    (hs : ∀ x ∈ s, p x ≠ 0 → q x ≠ 0) (hQ : ∑ x ∈ s, q x ≤ Q) :
    (∑ x ∈ s, p x) * Real.log ((∑ x ∈ s, p x) / Q) ≤
      ∑ x ∈ s, p x * Real.log (p x / q x) := by
  let P := ∑ x ∈ s, p x
  have hP0 : 0 ≤ P := sum_nonneg hp
  have hQ0 : 0 ≤ Q := (sum_nonneg hq).trans hQ
  by_cases hP : P = 0
  · have hzero : ∀ x ∈ s, p x = 0 := by
      intro x hx
      have hle := single_le_sum hp hx
      exact le_antisymm (by change p x ≤ P at hle; linarith) (hp x hx)
    have hz : (∑ x ∈ s, p x * Real.log (p x / q x)) = 0 :=
      sum_eq_zero (fun x hx => by rw [hzero x hx, zero_mul])
    change P * Real.log (P/Q) ≤ _
    rw [hP, zero_mul, hz]
  have hPn : 0 < P := lt_of_le_of_ne hP0 (Ne.symm hP)
  have hQn : Q ≠ 0 := mass_support s p q Q hp hq hs hQ hP
  have hQp : 0 < Q := lt_of_le_of_ne hQ0 (Ne.symm hQn)
  have hpoint : ∀ x ∈ s, p x * Real.log (P/Q) + p x - (P/Q)*q x ≤
      p x * Real.log (p x / q x) := by
    intro x hx
    by_cases hpx : p x = 0
    · simp only [hpx, zero_mul, zero_add, zero_sub]
      exact neg_nonpos.mpr (mul_nonneg (div_nonneg hP0 hQ0) (hq x hx))
    have hqp := hs x hx hpx
    have hpp : 0 < p x := lt_of_le_of_ne (hp x hx) (Ne.symm hpx)
    have hqq : 0 < q x := lt_of_le_of_ne (hq x hx) (Ne.symm hqp)
    have hr : 0 < q x * P / (p x * Q) := div_pos (mul_pos hqq hPn) (mul_pos hpp hQp)
    have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hr) (hp x hx)
    have he : Real.log (q x * P / (p x * Q)) =
        Real.log (P/Q) - Real.log (p x/q x) := by
      rw [Real.log_div (mul_ne_zero hqp hP) (mul_ne_zero hpx hQn),
        Real.log_mul hqp hP, Real.log_mul hpx hQn,
        Real.log_div hP hQn, Real.log_div hpx hqp]
      ring
    have hcancel : p x * (q x * P / (p x * Q)) = (P/Q)*q x := by
      field_simp
      <;> ring
    rw [he] at hl
    nlinarith
  have ht := sum_le_sum hpoint
  simp only [sum_sub_distrib, sum_add_distrib, ← sum_mul, ← mul_sum] at ht
  have hdef : (∑ x ∈ s, p x) = P := rfl
  rw [hdef] at ht
  have hle := mul_le_mul_of_nonneg_left hQ (div_nonneg hP0 hQ0)
  have hcancel : (P/Q)*Q = P := div_mul_cancel₀ P hQn
  change P * Real.log (P/Q) ≤ _
  nlinarith

theorem solution {α : Type} [Fintype α] (p : FinDist α) (q : α → ℝ)
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x ≤ 1) :
    ((1 / (2 * Real.log 2) * classicalTraceDist p.prob q ^ 2 : ℝ) : EReal) ≤
      relEntropy p q := by
  classical
  by_cases hsupp : Function.support p.prob ⊆ Function.support q
  · let s := univ.filter (fun x => q x ≤ p.prob x)
    let c := univ.filter (fun x => ¬ q x ≤ p.prob x)
    let a : ℝ := ∑ x ∈ s, p.prob x
    let b : ℝ := ∑ x ∈ s, q x
    have hsplit (f : α → ℝ) : (∑ x ∈ s, f x) + (∑ x ∈ c, f x) = ∑ x, f x := by
      dsimp [s, c]
      rw [sum_filter, sum_filter, ← sum_add_distrib]
      apply sum_congr rfl
      intro x hx
      by_cases h : q x ≤ p.prob x <;> simp [h]
    have ha0 : 0 ≤ a := sum_nonneg (fun x hx => p.nonneg x)
    have hb0 : 0 ≤ b := sum_nonneg (fun x hx => hq0 x)
    have hpc : (∑ x ∈ c, p.prob x) = 1-a := by
      have h := hsplit p.prob
      rw [p.sum_eq_one] at h
      change a + _ = 1 at h
      linarith
    have hqc : (∑ x ∈ c, q x) ≤ 1-b := by
      have h := hsplit q
      change b + _ = _ at h
      linarith
    have ha1 : a ≤ 1 := by
      have hh := sum_nonneg (fun x (_ : x ∈ c) => p.nonneg x)
      rw [hpc] at hh
      linarith
    have hb1 : b ≤ 1 := by
      have hh := sum_nonneg (fun x (_ : x ∈ c) => hq0 x)
      linarith
    have hs0 : a ≠ 0 → b ≠ 0 := mass_support s p.prob q b
      (fun x hx => p.nonneg x) (fun x hx => hq0 x) (fun x hx hp => hsupp hp) le_rfl
    have hs1 : 1-a ≠ 0 → 1-b ≠ 0 := by
      rw [← hpc]
      exact mass_support c p.prob q (1-b) (fun x hx => p.nonneg x)
        (fun x hx => hq0 x) (fun x hx hp => hsupp hp) hqc
    have hlower0 := logsum_bound s p.prob q b (fun x hx => p.nonneg x)
      (fun x hx => hq0 x) (fun x hx hp => hsupp hp) le_rfl
    have hlower1 := logsum_bound c p.prob q (1-b) (fun x hx => p.nonneg x)
      (fun x hx => hq0 x) (fun x hx hp => hsupp hp) hqc
    change a * Real.log (a/b) ≤ _ at hlower0
    rw [hpc] at hlower1
    have hcoarse : a*Real.log (a/b) + (1-a)*Real.log ((1-a)/(1-b)) ≤
        ∑ x, p.prob x * Real.log (p.prob x/q x) := by
      rw [← hsplit]
      exact add_le_add hlower0 hlower1
    let p2 : FinDist (Fin 2) :=
      ⟨![a,1-a], (by intro i; fin_cases i <;> simp [ha0, sub_nonneg.mpr ha1]),
        (by simp [Fin.sum_univ_two])⟩
    have hsupport2 : Function.support p2.prob ⊆ Function.support ![b,1-b] := by
      intro i hi
      fin_cases i
      · exact hs0 hi
      · exact hs1 hi
    have hbin := WildeQIT.PinskerRefined.lemma_10_8_1 p2 b hb0 hb1
    rw [relEntropy, if_pos hsupport2, ← EReal.coe_mul] at hbin
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hbinary : 2*(a-b)^2 ≤ a*Real.log (a/b) + (1-a)*Real.log ((1-a)/(1-b)) := by
      have hreal : 2*(a-b)^2 ≤ Real.log 2 *
          (a*Real.logb 2 (a/b) + (1-a)*Real.logb 2 ((1-a)/(1-b))) := by
        have hh : ((2*(a-b)^2 : ℝ) : EReal) ≤
            ((Real.log 2 * (a*Real.logb 2 (a/b) + (1-a)*Real.logb 2 ((1-a)/(1-b))) : ℝ) : EReal) := by
          simpa [p2, Fin.sum_univ_two] using hbin
        exact_mod_cast hh
      have he : Real.log 2 * (a*Real.logb 2 (a/b) + (1-a)*Real.logb 2 ((1-a)/(1-b))) =
          a*Real.log (a/b) + (1-a)*Real.log ((1-a)/(1-b)) := by
        simp only [Real.logb]
        field_simp [ne_of_gt hl2]
      rwa [he] at hreal
    have hab : 0 ≤ a-b := by
      change 0 ≤ (∑ x ∈ s, p.prob x) - ∑ x ∈ s, q x
      rw [← sum_sub_distrib]
      exact sum_nonneg (fun x hx => sub_nonneg.mpr (mem_filter.mp hx).2)
    have htrace : classicalTraceDist p.prob q ≤ 2*(a-b) := by
      have hp : ∀ x, |p.prob x-q x| =
          2*(if q x ≤ p.prob x then p.prob x-q x else 0) - (p.prob x-q x) := by
        intro x
        split_ifs with h
        · rw [abs_of_nonneg (sub_nonneg.mpr h)]; ring
        · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]; ring
      unfold classicalTraceDist
      simp_rw [hp]
      rw [sum_sub_distrib, ← mul_sum, ← sum_filter, sum_sub_distrib, sum_sub_distrib,
        p.sum_eq_one]
      change 2*(a-b) - (1 - ∑ x, q x) ≤ _
      linarith
    have ht0 : 0 ≤ classicalTraceDist p.prob q := sum_nonneg (fun x hx => abs_nonneg _)
    have hsquares : classicalTraceDist p.prob q ^ 2 ≤ 4*(a-b)^2 := by
      have hm := mul_nonneg (sub_nonneg.mpr htrace)
        (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hab) ht0)
      nlinarith
    have hS : classicalTraceDist p.prob q ^ 2 ≤
        2 * (∑ x, p.prob x * Real.log (p.prob x / q x)) := by linarith
    have hfinal : 1/(2*Real.log 2)*classicalTraceDist p.prob q ^ 2 ≤
        (∑ x, p.prob x * Real.log (p.prob x / q x)) / Real.log 2 := by
      apply (le_div_iff₀ hl2).mpr
      have he : 1/(2*Real.log 2)*classicalTraceDist p.prob q ^ 2 * Real.log 2 =
          classicalTraceDist p.prob q ^ 2 / 2 := by field_simp [ne_of_gt hl2] <;> ring
      rw [he]
      linarith
    rw [relEntropy, if_pos hsupp]
    have hbits : (∑ x, p.prob x * Real.logb 2 (p.prob x / q x)) =
        (∑ x, p.prob x * Real.log (p.prob x / q x)) / Real.log 2 := by
      simp only [Real.logb, mul_div_assoc, sum_div]
    rw [hbits]
    exact_mod_cast hfinal
  · rw [relEntropy, if_neg hsupp]
    exact le_top
