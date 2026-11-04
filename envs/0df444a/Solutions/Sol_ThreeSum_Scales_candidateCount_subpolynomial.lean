-- Prove2me | solution 1 for ThreeSum.Scales.candidateCount_subpolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:16.282398+00:00
-- url     : https://prove2.me/submissions/329cff00-18b6-495d-a095-c3c791c5a2bf

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Sqrt
import Definitions.Def_Submission_ThreeSum_Scales
import Theorems.Thm_ThreeSum_Scales_eventually_le_rpow_of_log_ratio
import Theorems.Thm_ThreeSum_Scales_primeWindow_ge_two
import Theorems.Thm_ThreeSum_Scales_primeWindow_log_ratio_tendsto_zero
import Theorems.Thm_ThreeSum_Asymptotics_log_nat_tendsto_atTop
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (candidateCount n : ℝ) ≤ (n : ℝ) ^ d := by
  have hc : Tendsto (fun n : ℕ => Real.log (4 * primeWindow n : ℝ) / Real.log n) atTop (𝓝 0) := by
    have hh := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 4)
    have h := hh.add primeWindow_log_ratio_tendsto_zero
    simp only [mul_zero, zero_add] at h
    apply h.congr'
    filter_upwards [] with n
    have hynz : (primeWindow n : ℝ) ≠ 0 := by
      exact_mod_cast (by have := primeWindow_ge_two n; omega : primeWindow n ≠ 0)
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hynz]
    simp only [Pi.inv_apply, add_div]
    ring
  have hbound : ∀ᶠ n : ℕ in atTop, ((4 * primeWindow n : ℕ) : ℝ) ≤ (n : ℝ) ^ d := by
    have h := eventually_le_rpow_of_log_ratio (a := 0) (f := fun n => 4 * primeWindow n) (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hc) hd
    simpa only [zero_add] using h
  filter_upwards [hbound] with n hn
  have hcard : candidateCount n ≤ 4 * primeWindow n := by
    unfold candidateCount PrimeDensity.candidates
    calc
      _ ≤ (Nat.primesLE (4 * primeWindow n)).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ 4 * primeWindow n := by
        rw [Nat.primesLE_eq_filter_Ioc_zero]
        exact (Finset.card_filter_le _ _).trans_eq (by simp)
  have hcardR : (candidateCount n : ℝ) ≤ ((4 * primeWindow n : ℕ) : ℝ) := by exact_mod_cast hcard
  exact hcardR.trans hn
end ThreeSum.Scales
