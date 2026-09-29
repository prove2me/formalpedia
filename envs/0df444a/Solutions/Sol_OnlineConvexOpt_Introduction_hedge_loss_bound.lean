-- Prove2me | solution 1 for OnlineConvexOpt.Introduction.hedge_loss_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T02:18:18.361266+00:00
-- url     : https://prove2.me/submissions/58ce470b-b741-49d4-a260-93fe968fd7dc

import Mathlib
import Definitions.Def_OnlineConvexOpt_Introduction_Hedge

namespace OnlineConvexOpt.Introduction

lemma oc_exp_ub {y : ℝ} (hy : 0 ≤ y) : Real.exp (-y) ≤ 1 - y + y ^ 2 := by
  rcases le_or_gt y 1 with h | h
  · have := Real.abs_exp_sub_one_sub_id_le (x := -y) (by rw [abs_neg, abs_of_nonneg hy]; exact h)
    have := (abs_le.mp this).2
    nlinarith
  · have := Real.exp_le_one_iff.mpr (by linarith : -y ≤ 0)
    nlinarith

theorem oc_hedge {N : ℕ} (hN : 0 < N) (ε : ℝ) (hε : 0 < ε)
    (ℓ x W : ℕ → Fin N → ℝ) (hnonneg : ∀ t i, 0 ≤ ℓ t i)
    (hrun : IsHedgeRun ε ℓ W x) (T : ℕ) (istar : Fin N) :
    expectedLoss x ℓ T ≤
      expertLoss ℓ istar T + ε * expectedLoss x (fun t i => ℓ t i ^ 2) T + Real.log N / ε := by
  have hW : ∀ t j, W t j = Real.exp (-ε * ∑ s ∈ Finset.range t, ℓ s j) := by
    intro t j
    induction t with
    | zero => simp [hrun.weight_init]
    | succ t ih =>
      rw [hrun.weight_update, ih, ← Real.exp_add, Finset.sum_range_succ]
      congr 1; ring
  have hWpos : ∀ t j, 0 < W t j := fun t j => by rw [hW]; exact Real.exp_pos _
  have hNe : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hΦpos : ∀ t, 0 < ∑ j, W t j := fun t => Finset.sum_pos (fun j _ => hWpos t j)
    Finset.univ_nonempty
  have hx : ∀ t j, x t j = W t j / ∑ k, W t k := hrun.prob_def
  have hxsum : ∀ t, ∑ j, x t j = 1 := by
    intro t; simp only [hx, ← Finset.sum_div]; exact div_self (hΦpos t).ne'
  have hxnn : ∀ t j, 0 ≤ x t j := fun t j => by
    rw [hx]; exact div_nonneg (hWpos t j).le (hΦpos t).le
  set a : ℕ → ℝ := fun t => ∑ j, x t j * ℓ t j with ha
  set b : ℕ → ℝ := fun t => ∑ j, x t j * ℓ t j ^ 2 with hb
  have hstep : ∀ t, (∑ j, W (t + 1) j) ≤ (∑ j, W t j) * Real.exp (-ε * a t + ε ^ 2 * b t) := by
    intro t
    have h1 : ∑ j, W (t + 1) j = (∑ j, W t j) * ∑ j, x t j * Real.exp (-ε * ℓ t j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hrun.weight_update, hx]
      field_simp [(hΦpos t).ne']
    have h2 : ∑ j, x t j * Real.exp (-ε * ℓ t j) ≤ 1 - ε * a t + ε ^ 2 * b t := by
      have : ∀ j, x t j * Real.exp (-ε * ℓ t j) ≤
          x t j * (1 - ε * ℓ t j + (ε * ℓ t j) ^ 2) := by
        intro j
        apply mul_le_mul_of_nonneg_left _ (hxnn t j)
        have := oc_exp_ub (mul_nonneg hε.le (hnonneg t j))
        rw [neg_mul]; exact this
      calc ∑ j, x t j * Real.exp (-ε * ℓ t j)
          ≤ ∑ j, x t j * (1 - ε * ℓ t j + (ε * ℓ t j) ^ 2) := Finset.sum_le_sum fun j _ => this j
        _ = 1 - ε * a t + ε ^ 2 * b t := by
          simp only [ha, hb, mul_add, mul_sub, mul_one, Finset.sum_add_distrib,
            Finset.sum_sub_distrib, hxsum, Finset.mul_sum]
          congr 1
          · congr 1; exact Finset.sum_congr rfl fun j _ => by ring
          · exact Finset.sum_congr rfl fun j _ => by ring
    have h3 : 1 - ε * a t + ε ^ 2 * b t ≤ Real.exp (-ε * a t + ε ^ 2 * b t) := by
      have := Real.add_one_le_exp (-ε * a t + ε ^ 2 * b t); linarith
    rw [h1]
    exact mul_le_mul_of_nonneg_left (h2.trans h3) (hΦpos t).le
  have hpot : ∀ t, (∑ j, W t j) ≤
      N * Real.exp (-ε * (∑ s ∈ Finset.range t, a s) + ε ^ 2 * ∑ s ∈ Finset.range t, b s) := by
    intro t
    induction t with
    | zero => simp [hrun.weight_init]
    | succ t ih =>
      calc (∑ j, W (t + 1) j) ≤ (∑ j, W t j) * Real.exp (-ε * a t + ε ^ 2 * b t) := hstep t
        _ ≤ (N * Real.exp (-ε * (∑ s ∈ Finset.range t, a s) +
              ε ^ 2 * ∑ s ∈ Finset.range t, b s)) * Real.exp (-ε * a t + ε ^ 2 * b t) :=
            mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
        _ = _ := by
            rw [mul_assoc, ← Real.exp_add, Finset.sum_range_succ, Finset.sum_range_succ]
            congr 2; ring
  have hA : expectedLoss x ℓ T = ∑ s ∈ Finset.range T, a s := rfl
  have hB : expectedLoss x (fun t i => ℓ t i ^ 2) T = ∑ s ∈ Finset.range T, b s := rfl
  have hL : expertLoss ℓ istar T = ∑ s ∈ Finset.range T, ℓ s istar := rfl
  have hle : Real.exp (-ε * ∑ s ∈ Finset.range T, ℓ s istar) ≤
      N * Real.exp (-ε * (∑ s ∈ Finset.range T, a s) + ε ^ 2 * ∑ s ∈ Finset.range T, b s) := by
    rw [← hW T istar]
    refine le_trans ?_ (hpot T)
    exact Finset.single_le_sum (fun j _ => (hWpos T j).le) (Finset.mem_univ istar)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog := Real.log_le_log (Real.exp_pos _) hle
  rw [Real.log_exp, Real.log_mul hNpos.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  rw [hA, hB, hL]
  set A := ∑ s ∈ Finset.range T, a s
  set B := ∑ s ∈ Finset.range T, b s
  set L := ∑ s ∈ Finset.range T, ℓ s istar
  have key : ε * A ≤ ε * L + ε ^ 2 * B + Real.log N := by linarith
  have e : L + ε * B + Real.log N / ε - A = (ε * L + ε ^ 2 * B + Real.log N - ε * A) / ε := by
    field_simp
  have : 0 ≤ L + ε * B + Real.log N / ε - A := by
    rw [e]; exact div_nonneg (by linarith) hε.le
  linarith

end OnlineConvexOpt.Introduction

open OnlineConvexOpt.Introduction

theorem solution {N : ℕ} (hN : 0 < N) (ε : ℝ) (hε : 0 < ε)
    (ℓ x W : ℕ → Fin N → ℝ) (hnonneg : ∀ t i, 0 ≤ ℓ t i)
    (hrun : IsHedgeRun ε ℓ W x) (T : ℕ) (istar : Fin N) :
    expectedLoss x ℓ T ≤
      expertLoss ℓ istar T + ε * expectedLoss x (fun t i => ℓ t i ^ 2) T + Real.log N / ε := by
  exact oc_hedge hN ε hε ℓ x W hnonneg hrun T istar
