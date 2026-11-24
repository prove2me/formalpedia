-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T01:04:43.221685+00:00
-- url     : https://prove2.me/submissions/c00bd366-1d93-4a14-ae55-877082875a4c

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_queryComplexity
import Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_4_5
import Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_4_6
import Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_C_1

open QuantumLTF.Membership.Supplement

theorem solution :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ k : ℕ, 2 ≤ k →
      (∀ n : ℕ, 2 * k ≤ n →
        c * Real.log k ≤ queryComplexity n (fun A => A.card = k) ∧
        (queryComplexity n (fun A => A.card = k) : ℝ) ≤ C * Real.log k) ∧
      (∀ n : ℕ, k ≤ n →
        c * Real.log k ≤ queryComplexity n (fun A => 1 ≤ A.card ∧ A.card ≤ k) ∧
        (queryComplexity n (fun A => 1 ≤ A.card ∧ A.card ≤ k) : ℝ) ≤ C * Real.log k) := by
  obtain ⟨⟨C, hC_pos, h45⟩, _⟩ := theorem_4_5
  obtain ⟨c₁, hc₁_pos, h46⟩ := theorem_4_6
  obtain ⟨_, ⟨c₂, hc₂_pos, hC1⟩⟩ := theorem_C_1
  refine ⟨min c₁ c₂, C, lt_min hc₁_pos hc₂_pos, hC_pos, ?_⟩
  intro k hk
  have hlog_nonneg : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
  refine ⟨fun n h2kn => ?_, fun n hkn => ?_⟩
  · have hkn : k ≤ n := by omega
    refine ⟨?_, (h45 k n hk hkn).2⟩
    exact le_trans (mul_le_mul_of_nonneg_right (min_le_right c₁ c₂) hlog_nonneg) (hC1 n k hk h2kn)
  · refine ⟨?_, (h45 k n hk hkn).1⟩
    exact le_trans (mul_le_mul_of_nonneg_right (min_le_left c₁ c₂) hlog_nonneg) (h46 n k hk hkn)
