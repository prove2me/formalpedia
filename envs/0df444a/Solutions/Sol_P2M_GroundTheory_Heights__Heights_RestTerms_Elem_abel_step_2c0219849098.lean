-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_abel_step_2c0219849098
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:24:32.657613+00:00
-- url     : https://prove2.me/submissions/46d3c4ae-ffc2-492e-9048-453f248be744

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_primeWeight_nonneg_6255b916e79a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_sum_primeWeight_le_932b2b356f63
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_primeWeight_eq_zero_of_lt_0f940253db51

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.Elem
namespace GroundTheory.Heights₂.Heights.RestTerms.Elem
theorem _root_.solution (B : ℝ) (hB : 0 < B) (j : ℕ) :
    (∑ i ∈ range (⌊B⌋₊ + 1 + j), primeWeight B i / (i : ℝ) ^ 2) -
        (∑ i ∈ range (⌊B⌋₊ + 1 + j), primeWeight B i) / ((⌊B⌋₊ + 1 + j : ℕ) : ℝ) ^ 2 ≤
      2 * Real.log 4 * (1 / ((⌊B⌋₊ + 1 : ℕ) : ℝ) - 1 / ((⌊B⌋₊ + 1 + j : ℕ) : ℝ)) := by
  set M := ⌊B⌋₊ + 1 with hM
  induction j with
  | zero =>
    have h0 : ∀ i ∈ range (M + 0), primeWeight B i = 0 := fun i hi =>
      primeWeight_eq_zero_of_lt B hB.le (by have := Finset.mem_range.mp hi; omega)
    rw [Finset.sum_eq_zero (fun i hi => by rw [h0 i hi, zero_div]),
      Finset.sum_eq_zero h0]
    simp
  | succ j ih =>
    set K := M + j with hK
    have hK1 : (1 : ℝ) ≤ K := by
      have : 1 ≤ K := by omega
      exact_mod_cast this
    have hKpos : (0 : ℝ) < K := by linarith
    rw [show M + (j + 1) = K + 1 by omega] at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    set S := ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2
    set G := ∑ i ∈ range K, primeWeight B i
    set g := primeWeight B K
    have hG1 : G + g ≤ K * Real.log 4 := by
      have := sum_primeWeight_le B K
      rw [Finset.sum_range_succ] at this
      exact this
    have hG1nn : 0 ≤ G + g := by
      have : 0 ≤ ∑ i ∈ range (K + 1), primeWeight B i :=
        Finset.sum_nonneg (fun i _ => primeWeight_nonneg B i)
      rw [Finset.sum_range_succ] at this
      exact this
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    push_cast at ih ⊢

    have hdiff : (S + g / (K : ℝ) ^ 2 - (G + g) / ((K : ℝ) + 1) ^ 2) -
        (S - G / (K : ℝ) ^ 2) = (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) := by
      field_simp
      ring
    have hnn : 0 ≤ 1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2 := by
      rw [sub_nonneg]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hstep : (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) ≤
        2 * Real.log 4 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) := by
      calc (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2)
          ≤ (K * Real.log 4) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) :=
            mul_le_mul_of_nonneg_right hG1 hnn
        _ = Real.log 4 * ((2 * K + 1) / (K * ((K : ℝ) + 1) ^ 2)) := by
            field_simp
            ring
        _ ≤ Real.log 4 * (2 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1))) := by
            apply mul_le_mul_of_nonneg_left _ hlog4
            rw [show (2 : ℝ) * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) = 2 / (K * ((K : ℝ) + 1)) by
              field_simp; ring]
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
        _ = 2 * Real.log 4 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) := by ring
    have ih' : S - G / (K : ℝ) ^ 2 ≤ 2 * Real.log 4 * (1 / ((M : ℕ) : ℝ) - 1 / (K : ℝ)) := by
      simpa using ih
    have : S + g / (K : ℝ) ^ 2 - (G + g) / ((K : ℝ) + 1) ^ 2 ≤
        2 * Real.log 4 * (1 / ((M : ℕ) : ℝ) - 1 / ((K : ℝ) + 1)) := by
      linarith
    simpa using this
end GroundTheory.Heights₂.Heights.RestTerms.Elem
