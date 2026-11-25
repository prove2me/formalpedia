-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_int_step_09746dc8c802
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:51:14.616261+00:00
-- url     : https://prove2.me/submissions/a1ad031e-e93d-40ce-b9c6-06b0ece3fe58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_log_div_sq_le_phiT_sub_469330899d5f

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
theorem _root_.solution (B₀ : ℝ) (hB : 16 ≤ B₀) (j : ℕ) :
    ∑ m ∈ range (⌊B₀⌋₊ + 1 + j), intWeight B₀ m ≤
      phiT (⌊B₀⌋₊ : ℝ) - phiT ((⌊B₀⌋₊ + j : ℕ) : ℝ) := by
  set n := ⌊B₀⌋₊ with hn
  have hn16 : 16 ≤ n := by
    rw [hn]; exact Nat.le_floor (by exact_mod_cast hB)
  induction j with
  | zero =>
    rw [Finset.sum_eq_zero]
    · simp
    · intro m hm
      have hm' : m ≤ n := by have := Finset.mem_range.mp hm; omega
      unfold intWeight
      rw [if_neg]
      intro h
      have : (m : ℝ) ≤ B₀ := by
        have := (Nat.le_floor_iff (by linarith)).mp hm'
        exact this
      linarith
  | succ j ih =>
    rw [show n + 1 + (j + 1) = (n + 1 + j) + 1 by omega, Finset.sum_range_succ]
    have hw : intWeight B₀ (n + 1 + j) =
        Real.log ((n + j : ℕ) + 1 : ℝ) / (((n + j : ℕ) : ℝ) + 1) ^ 2 := by
      unfold intWeight
      rw [if_pos]
      · push_cast; ring_nf
      · have : B₀ < ((n + 1 : ℕ) : ℝ) := by
          rw [hn]; push_cast; exact Nat.lt_floor_add_one B₀
        have h2 : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 + j : ℕ) : ℝ) := by exact_mod_cast (by omega)
        linarith
    have hk := log_div_sq_le_phiT_sub ((n + j : ℕ) : ℝ)
      (by have : 3 ≤ n + j := by omega
          exact_mod_cast this)
    rw [hw]
    have : ((n + (j + 1) : ℕ) : ℝ) = ((n + j : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [this]
    linarith
end GroundTheory.Heights₂.Heights.RestTerms.Elem
