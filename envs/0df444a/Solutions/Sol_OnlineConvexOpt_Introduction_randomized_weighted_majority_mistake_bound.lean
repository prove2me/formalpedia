-- Prove2me | solution 1 for OnlineConvexOpt.Introduction.randomized_weighted_majority_mistake_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T02:18:17.778908+00:00
-- url     : https://prove2.me/submissions/7af64823-4b0b-4114-95d4-c6e03d987529

import Mathlib
import Definitions.Def_OnlineConvexOpt_Introduction_MistakeCounts
import Definitions.Def_OnlineConvexOpt_Introduction_RandomizedWeightedMajority

namespace OnlineConvexOpt.Introduction

lemma oc_log_lb {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : -x - x ^ 2 ≤ Real.log (1 - x) := by
  let h : ℝ → ℝ := fun y => Real.log (1 - y) + y + y * y
  have hd : ∀ y, y < 1 → HasDerivAt h (-(1 - y)⁻¹ + 1 + 2 * y) y := by
    intro y hy
    have e1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have e2 := (Real.hasDerivAt_log (by linarith : (1 - y) ≠ 0)).comp y e1
    have e3 := (e2.add (hasDerivAt_id y)).add ((hasDerivAt_id y).mul (hasDerivAt_id y))
    refine e3.congr_deriv ?_
    simp only [id]
    ring
  have hmono : MonotoneOn h (Set.Icc 0 (1 / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
    · intro y hy
      exact (hd y (by linarith [hy.2])).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hd y (by linarith [hy.2])).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hd y (by linarith [hy.2])).deriv]
      have hpos : 0 < 1 - y := by linarith [hy.2]
      have : (1 - y)⁻¹ ≤ 1 + 2 * y := by
        rw [inv_le_iff_one_le_mul₀ hpos]
        nlinarith [hy.1, hy.2]
      linarith
  have := hmono ⟨le_refl 0, by norm_num⟩ ⟨h0, h1⟩ h0
  simp only [h, sub_zero, Real.log_one, add_zero, mul_zero] at this
  nlinarith

lemma oc_count_succ (P : ℕ → Prop) [DecidablePred P] (t : ℕ) :
    ((Finset.range (t + 1)).filter P).card =
      ((Finset.range t).filter P).card + if P t then 1 else 0 := by
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

lemma oc_wm_weight {N : ℕ} (ε : ℝ) (expertPredict : ℕ → Fin N → Bool) (outcome : ℕ → Bool)
    (W : ℕ → Fin N → ℝ) (hinit : ∀ i, W 0 i = 1)
    (hupd : ∀ t i, W (t + 1) i =
      if expertPredict t i = outcome t then W t i else W t i * (1 - ε)) (t : ℕ) (i : Fin N) :
    W t i = (1 - ε) ^ (expertMistakes expertPredict outcome i t) := by
  induction t with
  | zero => simp [hinit, expertMistakes]
  | succ t ih =>
    rw [hupd, ih]
    unfold expertMistakes
    rw [oc_count_succ]
    by_cases h : expertPredict t i = outcome t
    · simp [h]
    · simp [h, pow_succ]

theorem oc_rwm {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (expertPredict : ℕ → Fin N → Bool) (outcome : ℕ → Bool) (W p : ℕ → Fin N → ℝ)
    (hrun : IsRandomizedWeightedMajorityRun ε expertPredict outcome W p)
    (T : ℕ) (i : Fin N) :
    expectedMistakes expertPredict outcome p T ≤
      (1 + ε) * (expertMistakes expertPredict outcome i T : ℝ) + Real.log N / ε := by
  obtain ⟨hε0, hε1⟩ := hε
  have hW := oc_wm_weight ε expertPredict outcome W hrun.weight_init hrun.weight_update
  have hWpos : ∀ t j, 0 < W t j := fun t j => by rw [hW]; exact pow_pos (by linarith) _
  have hNe : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hΦpos : ∀ t, 0 < ∑ j, W t j := fun t => Finset.sum_pos (fun j _ => hWpos t j)
    Finset.univ_nonempty
  set m : ℕ → ℝ := fun t => ∑ j, p t j * (if expertPredict t j ≠ outcome t then (1 : ℝ) else 0)
    with hm
  have hstep : ∀ t, (∑ j, W (t + 1) j) = (∑ j, W t j) * (1 - ε * m t) := by
    intro t
    have hm' : (∑ j, W t j) * m t =
        ∑ j, W t j * (if expertPredict t j ≠ outcome t then (1 : ℝ) else 0) := by
      simp only [hm, Finset.mul_sum, hrun.prob_def]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp [(hΦpos t).ne']
    rw [mul_sub, mul_one, mul_left_comm, hm', Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hrun.weight_update]
    split_ifs with h1 h2 <;> simp_all <;> ring
  have hpot : ∀ t, (∑ j, W t j) ≤ N * Real.exp (-ε * ∑ s ∈ Finset.range t, m s) := by
    intro t
    induction t with
    | zero => simp [hrun.weight_init]
    | succ t ih =>
      rw [hstep, Finset.sum_range_succ, mul_add, neg_mul, Real.exp_add, ← neg_mul]
      have h1 : 1 - ε * m t ≤ Real.exp (-(ε * m t)) := by
        have := Real.one_sub_le_exp_neg (ε * m t); linarith
      calc (∑ j, W t j) * (1 - ε * m t) ≤ (∑ j, W t j) * Real.exp (-(ε * m t)) :=
            mul_le_mul_of_nonneg_left h1 (hΦpos t).le
        _ ≤ (N * Real.exp (-ε * ∑ s ∈ Finset.range t, m s)) * Real.exp (-(ε * m t)) :=
            mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
        _ = _ := by rw [neg_mul]; ring
  set E := expectedMistakes expertPredict outcome p T with hE
  have hEm : E = ∑ s ∈ Finset.range T, m s := rfl
  set Mi := expertMistakes expertPredict outcome i T
  have hle : (1 - ε) ^ Mi ≤ N * Real.exp (-ε * E) := by
    rw [← hW T i, hEm]
    refine le_trans ?_ (hpot T)
    exact Finset.single_le_sum (fun j _ => (hWpos T j).le) (Finset.mem_univ i)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog := Real.log_le_log (pow_pos (by linarith) _) hle
  rw [Real.log_pow, Real.log_mul hNpos.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  have l1 := oc_log_lb hε0.le hε1.le
  have hMi : (0 : ℝ) ≤ Mi := Nat.cast_nonneg _
  have k1 : (Mi : ℝ) * (-ε - ε ^ 2) ≤ Mi * Real.log (1 - ε) := mul_le_mul_of_nonneg_left l1 hMi
  have key : E * ε ≤ Real.log N + Mi * (ε + ε ^ 2) := by nlinarith
  have e : (1 + ε) * (Mi : ℝ) + Real.log N / ε - E =
      (Real.log N + Mi * (ε + ε ^ 2) - E * ε) / ε := by field_simp; ring
  have : 0 ≤ (1 + ε) * (Mi : ℝ) + Real.log N / ε - E := by
    rw [e]; exact div_nonneg (by linarith) hε0.le
  linarith

end OnlineConvexOpt.Introduction

open OnlineConvexOpt.Introduction

theorem solution {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (expertPredict : ℕ → Fin N → Bool) (outcome : ℕ → Bool) (W p : ℕ → Fin N → ℝ)
    (hrun : IsRandomizedWeightedMajorityRun ε expertPredict outcome W p)
    (T : ℕ) (i : Fin N) :
    expectedMistakes expertPredict outcome p T ≤
      (1 + ε) * (expertMistakes expertPredict outcome i T : ℝ) + Real.log N / ε := by
  exact oc_rwm hN ε hε expertPredict outcome W p hrun T i
