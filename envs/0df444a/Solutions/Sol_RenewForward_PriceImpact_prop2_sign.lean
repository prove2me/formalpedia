-- Prove2me | solution 1 for RenewForward.PriceImpact.prop2_sign
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T12:04:21.38963+00:00
-- url     : https://prove2.me/submissions/e6e6e7f4-9fd7-41fb-952d-6237f2ceb6f8

import Mathlib
import Definitions.Def_RenewForward_PriceImpact_Setting
import Definitions.Def_RenewForward_PriceImpact_ClosedForms

namespace RenewForward.PriceImpact

end RenewForward.PriceImpact

open RenewForward.PriceImpact

theorem solution (M : Params) (m : Moments) (hlam : 0 < M.lam) (hNR : 1 ≤ M.NR)
    (hmu : 0 < m.muX) (hs2X : 0 < m.s2X) (hs2T : 0 ≤ m.s2T)
    (hζ : 27 * m.muX * m.s2X ≤ 4 * (M.NR : ℝ) * m.tauX) :
    0 ≤ alpha4 M m ∧ 0 < alpha2 M m ∧ alpha0 M m < 0 ∧
    ∃ ks : ℝ, 0 < ks ∧ spsPoly M m ks = 0 ∧
      (∀ k ∈ Set.Ico 0 ks, spsPoly M m k < 0) ∧ (∀ k : ℝ, ks < k → 0 < spsPoly M m k) := by
  have hN : (1 : ℝ) ≤ M.NR := by exact_mod_cast hNR
  have hN0 : (0 : ℝ) < M.NR := by linarith
  have h4 : 0 ≤ alpha4 M m := by
    unfold alpha4
    have : 0 ≤ 4 * (M.NR : ℝ) * m.tauX - 27 * m.muX * m.s2X := by linarith
    have : 0 ≤ 3 * M.lam ^ 2 * (27 + 8 * (M.NR : ℝ)) * m.s2X := by positivity
    nlinarith
  have hτ : 0 ≤ m.tauX := by
    have : 0 < 27 * m.muX * m.s2X := by positivity
    nlinarith
  have h2 : 0 < alpha2 M m := by
    unfold alpha2
    have hA : 0 < 18 * m.muX * M.NR * (2 * M.NR - 27) * m.s2X + 90 * (M.NR : ℝ) ^ 2 * m.tauX := by
      have e1 : 90 * (M.NR : ℝ) ^ 2 * m.tauX ≥ 90 * (M.NR : ℝ) / 4 * (27 * m.muX * m.s2X) := by
        have := mul_le_mul_of_nonneg_left hζ (by positivity : (0:ℝ) ≤ 90 * (M.NR : ℝ) / 4)
        nlinarith
      have : 0 < m.muX * m.s2X * (M.NR : ℝ) := by positivity
      have : 0 < m.muX * m.s2X * (M.NR : ℝ) ^ 2 := by positivity
      nlinarith
    have hB : 0 ≤ - 3 * M.lam * m.muX * (189 + 20 * M.NR) * m.s2T * m.s2X
        + 4 * M.lam * M.NR * (27 + 4 * M.NR) * m.s2T * m.tauX := by
      have hl : 0 ≤ M.lam * m.s2T := by positivity
      have e : 4 * (M.NR : ℝ) * m.tauX * (27 + 4 * M.NR) ≥ 27 * m.muX * m.s2X * (27 + 4 * M.NR) :=
        mul_le_mul_of_nonneg_right hζ (by positivity)
      have : 0 ≤ m.muX * m.s2X * (M.NR : ℝ) := by positivity
      have key : 0 ≤ (4 * (M.NR : ℝ) * (27 + 4 * M.NR) * m.tauX
          - 3 * m.muX * (189 + 20 * M.NR) * m.s2X) := by nlinarith
      nlinarith [mul_nonneg hl key]
    have : 0 < 18 * M.lam := by positivity
    nlinarith [mul_pos this (add_pos_of_pos_of_nonneg hA hB)]
  have h0 : alpha0 M m < 0 := by
    unfold alpha0
    have : 0 < 216 * M.lam ^ 2 * m.s2T ^ 2 + 3 * (M.NR : ℝ) ^ 2 * (45 + 8 * M.lam * m.s2T)
      + 2 * M.lam * M.NR * m.s2T * (171 + 16 * M.lam * m.s2T) := by positivity
    nlinarith
  refine ⟨h4, h2, h0, ?_⟩
  set a0 := alpha0 M m
  set a1 := alpha1 M m
  set a2 := alpha2 M m
  set a4 := alpha4 M m
  have hs : ∀ k, spsPoly M m k = a0 + a1 * k + a2 * k ^ 2 + a4 * k ^ 4 := fun k => rfl
  -- convexity-type inequality along rays from 0
  have ray : ∀ t r : ℝ, 0 ≤ t → t ≤ 1 →
      spsPoly M m (t * r) ≤ (1 - t) * a0 + t * spsPoly M m r := by
    intro t r ht0 ht1
    rw [hs, hs]
    have e1 : t ^ 2 - t ≤ 0 := by nlinarith
    have e2 : t ^ 4 - t ≤ 0 := by
      have : t ^ 3 ≤ 1 := pow_le_one₀ ht0 ht1
      nlinarith
    have : a0 + a1 * (t * r) + a2 * (t * r) ^ 2 + a4 * (t * r) ^ 4
        - ((1 - t) * a0 + t * (a0 + a1 * r + a2 * r ^ 2 + a4 * r ^ 4))
        = a2 * r ^ 2 * (t ^ 2 - t) + a4 * r ^ 4 * (t ^ 4 - t) := by ring
    have : a2 * r ^ 2 * (t ^ 2 - t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) e1
    have : a4 * r ^ 4 * (t ^ 4 - t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) e2
    linarith
  -- a point where s is positive
  set K : ℝ := (|a1| + |a0| + 1) / a2 + 1 with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ (|a1| + |a0| + 1) / a2 := by positivity
    linarith
  have hKpos : 0 < spsPoly M m K := by
    rw [hs]
    have hKa : a2 * K ≥ |a1| + |a0| + 1 := by
      have : a2 * ((|a1| + |a0| + 1) / a2) = |a1| + |a0| + 1 := by field_simp
      nlinarith
    have : a2 * K ^ 2 ≥ (|a1| + |a0| + 1) * K := by nlinarith
    have : a4 * K ^ 4 ≥ 0 := by positivity
    have : a1 * K ≥ - |a1| * K := by nlinarith [neg_abs_le a1]
    have : a0 ≥ - |a0| := neg_abs_le a0
    have : |a0| * K ≥ |a0| := by nlinarith [abs_nonneg a0]
    nlinarith
  have hcont : Continuous (spsPoly M m) := by
    have : spsPoly M m = fun k => a0 + a1 * k + a2 * k ^ 2 + a4 * k ^ 4 := funext hs
    rw [this]; fun_prop
  obtain ⟨ks, hksI, hks⟩ : ∃ ks ∈ Set.Icc 0 K, spsPoly M m ks = 0 := by
    have := intermediate_value_Icc (by linarith : (0:ℝ) ≤ K) hcont.continuousOn
    have h0mem : (0:ℝ) ∈ Set.Icc (spsPoly M m 0) (spsPoly M m K) := by
      constructor
      · rw [hs]; simp; linarith
      · linarith
    exact this h0mem
  have hks0 : 0 < ks := by
    rcases eq_or_lt_of_le hksI.1 with h | h
    · rw [← h] at hks; rw [hs] at hks; simp at hks; linarith
    · exact h
  refine ⟨ks, hks0, hks, ?_, ?_⟩
  · intro k hk
    set t := k / ks
    have ht0 : 0 ≤ t := div_nonneg hk.1 hks0.le
    have ht1 : t < 1 := (div_lt_one hks0).2 hk.2
    have hkt : k = t * ks := by simp [t]; field_simp
    have := ray t ks ht0 ht1.le
    rw [← hkt, hks] at this
    nlinarith
  · intro k hk
    have hk0 : 0 < k := lt_trans hks0 hk
    set t := ks / k
    have ht0 : 0 < t := div_pos hks0 hk0
    have ht1 : t < 1 := (div_lt_one hk0).2 hk
    have hkt : ks = t * k := by simp [t]; field_simp
    have := ray t k ht0.le ht1.le
    rw [← hkt, hks] at this
    have : 0 < (1 - t) * (-a0) := mul_pos (by linarith) (by linarith)
    by_contra hc
    push Not at hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ht0.le hc]
