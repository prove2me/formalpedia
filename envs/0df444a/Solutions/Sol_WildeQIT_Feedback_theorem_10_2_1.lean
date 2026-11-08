-- Prove2me | solution 1 for WildeQIT.Feedback.theorem_10_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:32:46.46691+00:00
-- url     : https://prove2.me/submissions/8e089420-fa02-4e11-a93f-d52491156ab5

import Mathlib
import Definitions.Def_WildeQIT_entropy
import Definitions.Def_WildeQIT_condEntropy

namespace Aux_WQ1021

open WildeQIT

variable {α β : Type} [Fintype α] [Fintype β]

theorem fst_ge (p : FinDist (α × β)) (x : α) (y : β) : p.prob (x, y) ≤ p.fst.prob x := by
  rw [FinDist.fst_prob]
  exact Finset.single_le_sum (f := fun y => p.prob (x, y)) (fun y _ => p.nonneg _) (Finset.mem_univ y)

theorem snd_ge (p : FinDist (α × β)) (x : α) (y : β) : p.prob (x, y) ≤ p.snd.prob y := by
  rw [FinDist.snd_prob]
  exact Finset.single_le_sum (f := fun x => p.prob (x, y)) (fun x _ => p.nonneg _) (Finset.mem_univ x)

noncomputable def T (p : FinDist (α × β)) (x : α) (y : β) : ℝ :=
  p.prob (x, y) * (Real.logb 2 (p.prob (x, y) / p.snd.prob y) - Real.logb 2 (p.fst.prob x))

theorem diff_eq (p : FinDist (α × β)) :
    entropy p.fst - condEntropy p = ∑ x, ∑ y, T p x y := by
  unfold entropy condEntropy T
  have h : ∑ x, p.fst.prob x * Real.logb 2 (p.fst.prob x) =
      ∑ x, ∑ y, p.prob (x, y) * Real.logb 2 (p.fst.prob x) := by
    apply Finset.sum_congr rfl; intro x _
    rw [FinDist.fst_prob, Finset.sum_mul]
  rw [h]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem T_ge (p : FinDist (α × β)) (x : α) (y : β) :
    (p.prob (x, y) - p.fst.prob x * p.snd.prob y) / Real.log 2 ≤ T p x y := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hP := p.nonneg (x, y)
  have hA : 0 ≤ p.fst.prob x := p.fst.nonneg x
  have hB : 0 ≤ p.snd.prob y := p.snd.nonneg y
  rcases hP.eq_or_lt with h0 | hpos
  · unfold T
    rw [← h0, zero_mul, zero_sub, neg_div]
    have : 0 ≤ p.fst.prob x * p.snd.prob y / Real.log 2 := by positivity
    linarith
  · have hApos : 0 < p.fst.prob x := lt_of_lt_of_le hpos (fst_ge p x y)
    have hBpos : 0 < p.snd.prob y := lt_of_lt_of_le hpos (snd_ge p x y)
    unfold T Real.logb
    rw [Real.log_div hpos.ne' hBpos.ne', div_le_iff₀ hL]
    have hk := Real.log_le_sub_one_of_pos
      (show 0 < p.fst.prob x * p.snd.prob y / p.prob (x, y) by positivity)
    rw [Real.log_div (by positivity) hpos.ne', Real.log_mul hApos.ne' hBpos.ne'] at hk
    have e : p.prob (x, y) * ((Real.log (p.prob (x, y)) - Real.log (p.snd.prob y)) / Real.log 2 -
        Real.log (p.fst.prob x) / Real.log 2) * Real.log 2 =
        p.prob (x, y) * (Real.log (p.prob (x, y)) - Real.log (p.snd.prob y) -
          Real.log (p.fst.prob x)) := by field_simp
    rw [e]
    have h2 : p.prob (x, y) * (p.fst.prob x * p.snd.prob y / p.prob (x, y) - 1) =
        p.fst.prob x * p.snd.prob y - p.prob (x, y) := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hk hpos.le]

theorem sumP (p : FinDist (α × β)) : ∑ x, ∑ y, p.prob (x, y) = 1 := by
  rw [← Fintype.sum_prod_type']; exact p.sum_eq_one

theorem sumQ (p : FinDist (α × β)) : ∑ x, ∑ y, p.fst.prob x * p.snd.prob y = 1 := by
  simp only [← Finset.mul_sum, ← Finset.sum_mul, p.snd.sum_eq_one, p.fst.sum_eq_one, mul_one]

theorem sum_lower (p : FinDist (α × β)) :
    ∑ x, ∑ y, (p.prob (x, y) - p.fst.prob x * p.snd.prob y) / Real.log 2 = 0 := by
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, sumP, sumQ, sub_self, zero_div]

end Aux_WQ1021

open WildeQIT Aux_WQ1021 in
theorem solution {α β : Type} [Fintype α] [Fintype β] (p : FinDist (α × β)) :
    condEntropy p ≤ entropy p.fst ∧ (condEntropy p = entropy p.fst ↔ p.Indep) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsum : 0 ≤ ∑ x, ∑ y, T p x y := by
    rw [← sum_lower p]
    exact Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => T_ge p x y))
  have hd := diff_eq p
  refine ⟨by linarith, ⟨fun heq => ?_, fun hind => ?_⟩⟩
  · -- equality forces independence
    have hzero : ∑ x, ∑ y, (T p x y -
        (p.prob (x, y) - p.fst.prob x * p.snd.prob y) / Real.log 2) = 0 := by
      simp only [Finset.sum_sub_distrib]
      rw [sum_lower]
      linarith
    have hnn : ∀ x y, 0 ≤ T p x y - (p.prob (x, y) - p.fst.prob x * p.snd.prob y) / Real.log 2 :=
      fun x y => sub_nonneg.mpr (T_ge p x y)
    have hx := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => Finset.sum_nonneg (fun y _ => hnn x y))).mp hzero
    intro x y
    have hy := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hnn x y)).mp
      (hx x (Finset.mem_univ _)) y (Finset.mem_univ _)
    have hP := p.nonneg (x, y)
    rcases hP.eq_or_lt with h0 | hpos
    · unfold T at hy
      rw [← h0, zero_mul, zero_sub] at hy
      have hq : p.fst.prob x * p.snd.prob y = 0 := by
        rw [zero_sub, neg_div, neg_neg] at hy
        exact (div_eq_zero_iff.mp hy).resolve_right hL.ne'
      rw [← h0, hq]
    · have hApos : 0 < p.fst.prob x := lt_of_lt_of_le hpos (fst_ge p x y)
      have hBpos : 0 < p.snd.prob y := lt_of_lt_of_le hpos (snd_ge p x y)
      by_contra hne
      have hne' : p.fst.prob x * p.snd.prob y / p.prob (x, y) ≠ 1 := by
        intro h
        rw [div_eq_one_iff_eq hpos.ne'] at h
        exact hne h.symm
      have hk := Real.log_lt_sub_one_of_pos
        (show 0 < p.fst.prob x * p.snd.prob y / p.prob (x, y) by positivity) hne'
      rw [Real.log_div (by positivity) hpos.ne', Real.log_mul hApos.ne' hBpos.ne'] at hk
      unfold T Real.logb at hy
      rw [Real.log_div hpos.ne' hBpos.ne'] at hy
      have e : p.prob (x, y) * ((Real.log (p.prob (x, y)) - Real.log (p.snd.prob y)) / Real.log 2 -
          Real.log (p.fst.prob x) / Real.log 2) -
          (p.prob (x, y) - p.fst.prob x * p.snd.prob y) / Real.log 2 =
          (p.prob (x, y) * (Real.log (p.prob (x, y)) - Real.log (p.snd.prob y) -
            Real.log (p.fst.prob x)) - (p.prob (x, y) - p.fst.prob x * p.snd.prob y)) /
            Real.log 2 := by
        field_simp
      rw [e, div_eq_zero_iff] at hy
      rcases hy with hy | hy
      · have h2 : p.prob (x, y) * (p.fst.prob x * p.snd.prob y / p.prob (x, y) - 1) =
            p.fst.prob x * p.snd.prob y - p.prob (x, y) := by field_simp
        nlinarith [mul_lt_mul_of_pos_left hk hpos]
      · exact hL.ne' hy
  · -- independence gives equality
    have hT : ∀ x y, T p x y = 0 := by
      intro x y
      unfold T
      have hP := p.nonneg (x, y)
      rcases hP.eq_or_lt with h0 | hpos
      · rw [← h0, zero_mul]
      · have hBpos : 0 < p.snd.prob y := lt_of_lt_of_le hpos (snd_ge p x y)
        have : p.prob (x, y) / p.snd.prob y = p.fst.prob x := by
          rw [hind x y]; field_simp
        rw [this, sub_self, mul_zero]
    have : ∑ x, ∑ y, T p x y = 0 := by simp [hT]
    linarith
