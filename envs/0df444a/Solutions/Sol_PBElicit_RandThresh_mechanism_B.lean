-- Prove2me | solution 1 for PBElicit.RandThresh.mechanism_B
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:42:32.250489+00:00
-- url     : https://prove2.me/submissions/22f73ab6-0357-4ad3-88d6-e2c7c7af72fd

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting

open Classical PBElicit.RandThresh

lemma pb_mem_bucket {A : Type*} [Fintype A] (c : A → ℝ) (m j : ℕ) (a : A) :
    a ∈ bucket c m j ↔ c a ∈ Ivl m j := by
  simp [bucket]

theorem solution {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (v : Fin n → A → ℝ) (hv : IsUtilityProfile v) (m K : ℕ) (hA : Fintype.card A = m)
    (hmK : m = 2 ^ K) (Sstar : Finset A) (hS : IsWelfareOptimal c v Sstar) :
    cost c (bucket c m 0) ≤ 1 ∧ sw v (Sstar ∩ bucket c m 0) ≤ sw v (bucket c m 0) := by
  have hm1 : (1:ℝ) ≤ m := by rw [hmK]; exact_mod_cast Nat.one_le_two_pow
  have hmpos : (0:ℝ) < m := by linarith
  refine ⟨?_, ?_⟩
  · unfold cost
    have hle : ∀ a ∈ bucket c m 0, c a ≤ 1 / (m:ℝ)^2 := by
      intro a ha
      have ha := (pb_mem_bucket c m 0 a).mp ha
      simp only [Ivl, if_pos rfl, Set.mem_Icc] at ha
      exact ha.2
    have h := Finset.sum_le_card_nsmul _ c _ hle
    rw [nsmul_eq_mul] at h
    have hcard : ((bucket c m 0).card : ℝ) ≤ m := by
      rw [← hA]; exact_mod_cast Finset.card_le_univ _
    have : ((bucket c m 0).card : ℝ) * (1 / (m:ℝ)^2) ≤ 1 := by
      calc ((bucket c m 0).card : ℝ) * (1 / (m:ℝ)^2) ≤ m * (1 / (m:ℝ)^2) := by gcongr
        _ = 1 / (m:ℝ) := by field_simp
        _ ≤ 1 := by rw [div_le_one hmpos]; exact hm1
    linarith
  · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun a _ _ => Finset.sum_nonneg (fun i _ => hv.1 i a))
