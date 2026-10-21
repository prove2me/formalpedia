-- Prove2me | solution 1 for RetailerMarketplace.Entry.proposition_1_sbt
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:40:49.180167+00:00
-- url     : https://prove2.me/submissions/8f7cd3c2-0c67-4fab-b54a-5e1b778c4b6a

import Mathlib
import Definitions.Def_RetailerMarketplace_Entry_Model
import Definitions.Def_RetailerMarketplace_Entry_PricingGame

set_option autoImplicit false
open RetailerMarketplace.Entry

theorem q_T_val (lam v p : ℝ) (hp : p ≤ v) : qT_SBT lam v p Steer.T = 1 := by
  unfold qT_SBT; simp [hp]

theorem q_gt (lam v p : ℝ) (S : Steer) (hp : v < p) : qT_SBT lam v p S = 0 := by
  unfold qT_SBT; simp [not_le.mpr hp]

theorem q_M_val (lam v p : ℝ) (hp : p ≤ v) : qT_SBT lam v p Steer.M = 1 - lam := by
  unfold qT_SBT; simp [hp]

theorem q_le_T (lam v p : ℝ) (hl0 : 0 ≤ lam) (S : Steer) :
    qT_SBT lam v p S ≤ qT_SBT lam v p Steer.T := by
  by_cases hp : p ≤ v
  · rw [q_T_val lam v p hp]
    cases S
    · rw [q_M_val lam v p hp]; linarith
    · rw [q_T_val lam v p hp]
  · rw [q_gt lam v p _ (not_le.mp hp), q_gt lam v p _ (not_le.mp hp)]

theorem q_M_le (lam v p : ℝ) (hl0 : 0 ≤ lam) (S : Steer) :
    qT_SBT lam v p Steer.M ≤ qT_SBT lam v p S := by
  by_cases hp : p ≤ v
  · rw [q_M_val lam v p hp]
    cases S
    · rw [q_M_val lam v p hp]
    · rw [q_T_val lam v p hp]; linarith
  · rw [q_gt lam v p _ (not_le.mp hp), q_gt lam v p _ (not_le.mp hp)]

theorem q_nonneg (lam v p : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (S : Steer) :
    0 ≤ qT_SBT lam v p S := by
  by_cases hp : p ≤ v
  · cases S
    · rw [q_M_val lam v p hp]; linarith
    · rw [q_T_val lam v p hp]; norm_num
  · rw [q_gt lam v p _ (not_le.mp hp)]

theorem solution (c f lam v : ℝ) (hc : 0 < c) (hf : f ∈ Set.Ico (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hv : c ≤ v * (1 - f)) :
    ∃ σ : ℝ → Steer, IsSPNE_SBT c f lam v v σ ∧ σ v = Steer.T ∧
      uT_SBT c f lam v v Steer.T = piSBT_T c f v ∧ uM_SBT f lam v v Steer.T = piSBT_M f v := by
  obtain ⟨hf0, hf1⟩ := hf
  obtain ⟨hl0, hl1⟩ := hlam
  have hv0 : 0 < v := by
    by_contra h
    push Not at h
    nlinarith
  have hfv : 0 ≤ (1 - f) * v - c := by nlinarith
  classical
  refine ⟨fun p => if 0 ≤ p then Steer.T else Steer.M, ⟨?_, ?_⟩, by simp [hv0.le], ?_, ?_⟩
  · intro p S
    unfold uM_SBT
    by_cases hp : 0 ≤ p
    · simp only [hp, if_true]
      have := q_le_T lam v p hl0 S
      have h2 : 0 ≤ f * p := mul_nonneg hf0 hp
      nlinarith
    · simp only [hp, if_false]
      have := q_M_le lam v p hl0 S
      have h2 : f * p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hf0 (le_of_not_ge hp)
      nlinarith
  · intro p
    show uT_SBT c f lam v p (if 0 ≤ p then Steer.T else Steer.M) ≤
      uT_SBT c f lam v v (if 0 ≤ v then Steer.T else Steer.M)
    simp only [hv0.le, if_true]
    unfold uT_SBT
    rw [q_T_val lam v v le_rfl]
    by_cases hpv : p ≤ v
    · by_cases hp : 0 ≤ p
      · simp only [hp, if_true]
        rw [q_T_val lam v p hpv]
        nlinarith
      · simp only [hp, if_false]
        have hq := q_nonneg lam v p hl0 hl1 Steer.M
        have : (1 - f) * p - c < 0 := by nlinarith [not_le.mp hp]
        nlinarith
    · have hq := q_gt lam v p (if 0 ≤ p then Steer.T else Steer.M) (not_le.mp hpv)
      rw [hq]
      nlinarith
  · unfold uT_SBT piSBT_T
    rw [q_T_val lam v v le_rfl]; ring
  · unfold uM_SBT piSBT_M
    rw [q_T_val lam v v le_rfl]; ring
