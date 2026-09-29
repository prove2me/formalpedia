-- Prove2me | solution 1 for OnlineConvexOpt.Introduction.weighted_majority_mistake_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T02:18:17.252595+00:00
-- url     : https://prove2.me/submissions/560e4993-06ca-42a7-ba3c-870515774f25

import Mathlib
import Definitions.Def_OnlineConvexOpt_Introduction_MistakeCounts
import Definitions.Def_OnlineConvexOpt_Introduction_WeightedMajority

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

theorem oc_wm {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (expertPredict : ℕ → Fin N → Bool) (outcome : ℕ → Bool) (W : ℕ → Fin N → ℝ)
    (algPredict : ℕ → Bool) (hrun : IsWeightedMajorityRun ε expertPredict outcome W algPredict)
    (T : ℕ) (i : Fin N) :
    (algMistakes algPredict outcome T : ℝ) ≤
      2 * (1 + ε) * (expertMistakes expertPredict outcome i T : ℝ) + 2 * Real.log N / ε := by
  obtain ⟨hε0, hε1⟩ := hε
  have hW := oc_wm_weight ε expertPredict outcome W hrun.weight_init hrun.weight_update
  have hWpos : ∀ t j, 0 < W t j := fun t j => by rw [hW]; exact pow_pos (by linarith) _
  -- the potential
  have hstep : ∀ t, (∑ j, W (t + 1) j) ≤
      (if algPredict t ≠ outcome t then 1 - ε / 2 else 1) * ∑ j, W t j := by
    intro t
    have hsplit : ∑ j, W (t + 1) j = ∑ j, W t j -
        ε * ∑ j ∈ Finset.univ.filter (fun j => expertPredict t j ≠ outcome t), W t j := by
      rw [Finset.mul_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hrun.weight_update]
      by_cases h : expertPredict t j = outcome t
      · simp [h]
      · simp [h]; ring
    have hwrong_nn : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j => expertPredict t j ≠ outcome t),
        W t j := Finset.sum_nonneg fun j _ => (hWpos t j).le
    split_ifs with herr
    · -- at least half of the weight is on mistaken experts
      have htot : ∑ j, W t j =
          (∑ j ∈ Finset.univ.filter (fun j => expertPredict t j = true), W t j) +
          (∑ j ∈ Finset.univ.filter (fun j => expertPredict t j = false), W t j) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => expertPredict t j = true)]
        congr 1
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext j; simp
      have hwrong : ∑ j ∈ Finset.univ.filter (fun j => expertPredict t j ≠ outcome t), W t j =
          ∑ j ∈ Finset.univ.filter (fun j => expertPredict t j = algPredict t), W t j := by
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        cases hp : expertPredict t j <;> cases ha : algPredict t <;> cases ho : outcome t <;>
          simp_all
      have hhalf : (∑ j, W t j) / 2 ≤
          ∑ j ∈ Finset.univ.filter (fun j => expertPredict t j ≠ outcome t), W t j := by
        rw [hwrong, htot]
        have hrule := hrun.predict_rule t
        cases ha : algPredict t
        · rw [ha] at hrule
          have : ¬ ((∑ j ∈ Finset.univ.filter (fun j => expertPredict t j = true), W t j) ≥
              (∑ j ∈ Finset.univ.filter (fun j => expertPredict t j = false), W t j)) := by
            intro h; have := hrule.mpr h; simp at this
          push Not at this
          linarith
        · rw [ha] at hrule
          have := hrule.mp rfl
          linarith
      rw [hsplit]
      nlinarith
    · rw [hsplit]
      nlinarith
  have hpot : ∀ t, (∑ j, W t j) ≤ N * (1 - ε / 2) ^ (algMistakes algPredict outcome t) := by
    intro t
    induction t with
    | zero => simp [hrun.weight_init, algMistakes]
    | succ t ih =>
      have hs := hstep t
      unfold algMistakes at ih ⊢
      rw [oc_count_succ]
      have hq : 0 ≤ 1 - ε / 2 := by linarith
      split_ifs at hs ⊢ with herr
      · rw [pow_succ]
        calc (∑ j, W (t + 1) j) ≤ (1 - ε / 2) * ∑ j, W t j := hs
          _ ≤ (1 - ε / 2) * (N * (1 - ε / 2) ^ ((Finset.range t).filter
              (fun t => algPredict t ≠ outcome t)).card) := mul_le_mul_of_nonneg_left ih hq
          _ = _ := by ring
      · simpa using hs.trans (by linarith)
  -- combine
  set M := algMistakes algPredict outcome T
  set Mi := expertMistakes expertPredict outcome i T
  have hle : (1 - ε) ^ Mi ≤ N * (1 - ε / 2) ^ M := by
    rw [← hW T i]
    refine le_trans ?_ (hpot T)
    exact Finset.single_le_sum (fun j _ => (hWpos T j).le) (Finset.mem_univ i)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog := Real.log_le_log (pow_pos (by linarith) _) hle
  rw [Real.log_pow, Real.log_mul hNpos.ne' (pow_pos (by linarith) _).ne', Real.log_pow] at hlog
  have l1 := oc_log_lb hε0.le hε1.le
  have l2 : Real.log (1 - ε / 2) ≤ -(ε / 2) := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 - ε / 2); linarith
  have hMi : (0 : ℝ) ≤ Mi := Nat.cast_nonneg _
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have k1 : (Mi : ℝ) * (-ε - ε ^ 2) ≤ Mi * Real.log (1 - ε) := mul_le_mul_of_nonneg_left l1 hMi
  have k2 : (M : ℝ) * Real.log (1 - ε / 2) ≤ M * (-(ε / 2)) := mul_le_mul_of_nonneg_left l2 hM
  have key : (M : ℝ) * ε ≤ 2 * (Real.log N + Mi * (ε + ε ^ 2)) := by nlinarith
  have e : 2 * (1 + ε) * (Mi : ℝ) + 2 * Real.log N / ε - M =
      (2 * (Real.log N + Mi * (ε + ε ^ 2)) - M * ε) / ε := by field_simp; ring
  have : 0 ≤ 2 * (1 + ε) * (Mi : ℝ) + 2 * Real.log N / ε - M := by
    rw [e]; exact div_nonneg (by linarith) hε0.le
  linarith

end OnlineConvexOpt.Introduction

open OnlineConvexOpt.Introduction

theorem solution {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (expertPredict : ℕ → Fin N → Bool) (outcome : ℕ → Bool) (W : ℕ → Fin N → ℝ)
    (algPredict : ℕ → Bool) (hrun : IsWeightedMajorityRun ε expertPredict outcome W algPredict)
    (T : ℕ) (i : Fin N) :
    (algMistakes algPredict outcome T : ℝ) ≤
      2 * (1 + ε) * (expertMistakes expertPredict outcome i T : ℝ) + 2 * Real.log N / ε := by
  exact oc_wm hN ε hε expertPredict outcome W algPredict hrun T i
