-- Prove2me | solution 1 for ThreeSum.Scales.log_bits_over_primeBase_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:50:12.759692+00:00
-- url     : https://prove2.me/submissions/733b166d-e9ef-4c27-a395-3f210da4f30f

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
import Theorems.Thm_ThreeSum_Scales_inputBits_tendsto_atTop
import Theorems.Thm_ThreeSum_Scales_primeWindow_ge_two
import Theorems.Thm_ThreeSum_Scales_log_bits_over_windowExponent_tendsto_zero
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
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (inputBits n + 1 : ℝ) /
      Real.log (4 * primeWindow n : ℝ)) atTop (𝓝 0) := by
  have hu := (log_bits_over_windowExponent_tendsto_zero.comp inputBits_tendsto_atTop).div_const
    (Real.log 2)
  simp only [zero_div] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [] with n
    have hy := primeWindow_ge_two n
    have hb : 0 ≤ Real.log (4 * primeWindow n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 4 * primeWindow n))
    have hn : 0 ≤ Real.log (inputBits n + 1 : ℝ) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (inputBits n); linarith)
    exact div_nonneg hn hb
  · filter_upwards [] with n
    have hy := primeWindow_ge_two n
    have hypo : (0 : ℝ) < primeWindow n := by exact_mod_cast (by omega : 0 < primeWindow n)
    have hly : 0 < Real.log (primeWindow n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < primeWindow n))
    have hlyb : Real.log (primeWindow n : ℝ) ≤ Real.log (4 * primeWindow n : ℝ) :=
      Real.log_le_log hypo (by linarith)
    have hn : 0 ≤ Real.log (inputBits n + 1 : ℝ) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (inputBits n); linarith)
    have hd := div_le_div_of_nonneg_left hn hly hlyb
    simpa only [Function.comp_def, primeWindow, Nat.cast_pow, Nat.cast_ofNat,
      Real.log_pow, div_div] using hd
end ThreeSum.Scales
