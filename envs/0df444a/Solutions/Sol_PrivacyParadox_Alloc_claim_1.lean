-- Prove2me | solution 1 for PrivacyParadox.Alloc.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:12:21.458555+00:00
-- url     : https://prove2.me/submissions/ae15c0f7-7023-4e90-97d8-c3975e00701b

import Mathlib
import Definitions.Def_PrivacyParadox_Alloc_Model

open PrivacyParadox.Alloc in
theorem solution (P : Prog) (hP : P.Standing) (m : ℕ) (hm1 : 1 ≤ m) (hmK : m < P.K) :
    P.Q m 1 < P.Q (m + 1) 1 ∧ P.R (m + 1) 1 < P.R m 1 ∧
      P.Q m 1 / P.R m 1 < P.Q (m + 1) 1 / P.R (m + 1) 1 := by
  obtain ⟨hK, hpos, hmono, hsumθ, hθ0, hθ1, hγ0, hγ1, hs, hB⟩ := hP
  have hmem : ∀ k, 1 ≤ k → k ≤ P.K → k ∈ Finset.Icc 1 P.K := fun k h1 h2 =>
    Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hφ : P.phi m < P.phi (m + 1) :=
    hmono (Set.mem_Icc.mpr ⟨hm1, hmK.le⟩) (Set.mem_Icc.mpr ⟨(by omega : 1 ≤ m + 1), hmK⟩) (by simp)
  have hφ0 : 0 < P.phi m := (hpos m (hmem m hm1 hmK.le)).2
  have hφ1 : 0 < P.phi (m + 1) := (hpos (m + 1) (hmem (m + 1) (by omega) hmK)).2
  have hpr : 0 < P.pr (m + 1) := (hpos (m + 1) (hmem (m + 1) (by omega) hmK)).1
  have hI : Finset.Icc (m + 1) P.K = insert (m + 1) (Finset.Icc (m + 1 + 1) P.K) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : m + 1 ∉ Finset.Icc (m + 1 + 1) P.K := by simp
  set S := ∑ k ∈ Finset.Icc 1 m, P.pr k * P.phi k with hSdef
  set T := ∑ k ∈ Finset.Icc (m + 1 + 1) P.K, P.pr k * Real.sqrt (P.phi k) with hTdef
  set U := ∑ k ∈ Finset.Icc (m + 1 + 1) P.K, P.pr k with hUdef
  have hS : 0 < S := by
    apply Finset.sum_pos
    · intro k hk
      rw [Finset.mem_Icc] at hk
      have := hpos k (hmem k hk.1 (by omega))
      exact mul_pos this.1 this.2
    · exact ⟨m, Finset.mem_Icc.mpr ⟨hm1, le_rfl⟩⟩
  have hT : 0 ≤ T := by
    apply Finset.sum_nonneg
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact mul_nonneg (hpos k (hmem k (by omega) hk.2)).1.le (Real.sqrt_nonneg _)
  have hU : 0 ≤ U := by
    apply Finset.sum_nonneg
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact (hpos k (hmem k (by omega) hk.2)).1.le
  have hQm : P.Q m 1 = S + Real.sqrt (P.phi m) * (P.pr (m + 1) * Real.sqrt (P.phi (m + 1)) + T) := by
    unfold Prog.Q
    rw [div_one, hI, Finset.sum_insert hnot]
  have hQm1 : P.Q (m + 1) 1 = S + P.pr (m + 1) * P.phi (m + 1) + Real.sqrt (P.phi (m + 1)) * T := by
    unfold Prog.Q
    rw [div_one, Finset.sum_Icc_succ_top (by omega)]
  have hRm : P.R m 1 = 2 * P.gam * (1 / P.phi m * S + (P.pr (m + 1) + U)) +
      P.theta ^ 2 * (1 - P.theta) * (1 - P.gam) * P.s := by
    unfold Prog.R
    rw [hI, Finset.sum_insert hnot]
  have hRm1 : P.R (m + 1) 1 = 2 * P.gam * (1 / P.phi (m + 1) * (S + P.pr (m + 1) * P.phi (m + 1)) + U) +
      P.theta ^ 2 * (1 - P.theta) * (1 - P.gam) * P.s := by
    unfold Prog.R
    rw [Finset.sum_Icc_succ_top (by omega)]
  set a := Real.sqrt (P.phi m) with ha
  set b := Real.sqrt (P.phi (m + 1)) with hb
  have hab : a < b := Real.sqrt_lt_sqrt hφ0.le hφ
  have ha0 : 0 < a := Real.sqrt_pos.mpr hφ0
  have hbb : b * b = P.phi (m + 1) := Real.mul_self_sqrt hφ1.le
  have hQ : P.Q m 1 < P.Q (m + 1) 1 := by
    rw [hQm, hQm1, ← hbb]
    nlinarith [mul_pos (mul_pos hpr (by linarith : (0:ℝ) < b)) (by linarith : (0:ℝ) < b - a),
      mul_nonneg (by linarith : (0:ℝ) ≤ b - a) hT]
  have hsR : (0 : ℝ) < P.s := by exact_mod_cast hs
  have hc : 0 ≤ P.theta ^ 2 * (1 - P.theta) * (1 - P.gam) * P.s := by
    have : 0 ≤ 1 - P.theta := by linarith
    have : 0 ≤ 1 - P.gam := by linarith
    positivity
  have e1 : 1 / P.phi (m + 1) * (S + P.pr (m + 1) * P.phi (m + 1)) =
      1 / P.phi (m + 1) * S + P.pr (m + 1) := by
    field_simp
  have hinv : 1 / P.phi (m + 1) * S < 1 / P.phi m * S :=
    mul_lt_mul_of_pos_right (one_div_lt_one_div_of_lt hφ0 hφ) hS
  have hR : P.R (m + 1) 1 < P.R m 1 := by
    rw [hRm, hRm1, e1]
    nlinarith [mul_lt_mul_of_pos_left hinv hγ0]
  have hR1pos : 0 < P.R (m + 1) 1 := by
    rw [hRm1, e1]
    have : 0 < 1 / P.phi (m + 1) * S := by positivity
    nlinarith
  have hRpos : 0 < P.R m 1 := by linarith
  have hQpos : 0 < P.Q m 1 := by
    rw [hQm]
    have : 0 ≤ a * (P.pr (m + 1) * b + T) := by
      exact mul_nonneg ha0.le (add_nonneg (mul_nonneg hpr.le (Real.sqrt_nonneg _)) hT)
    linarith
  refine ⟨hQ, hR, ?_⟩
  rw [div_lt_div_iff₀ hRpos hR1pos]
  exact (mul_lt_mul_of_pos_left hR hQpos).trans (mul_lt_mul_of_pos_right hQ hRpos)
