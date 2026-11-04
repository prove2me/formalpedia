-- Prove2me | solution 1 for ThreeSum.Scales.scoreBase_log_over_primeBase_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:54:50.052679+00:00
-- url     : https://prove2.me/submissions/29723f7e-5630-4ebb-8461-ed795ed34a31

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
import Theorems.Thm_ThreeSum_Scales_primeBase_log_tendsto_atTop
import Theorems.Thm_ThreeSum_Scales_log_bits_over_primeBase_tendsto_zero
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
theorem _root_.solution (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (16 * ((k : ℝ) + 2) * (inputBits n + 1)) /
      Real.log (4 * primeWindow n : ℝ)) atTop (𝓝 0) := by
  have hc := primeBase_log_tendsto_atTop.inv_tendsto_atTop.const_mul
    (Real.log (16 * ((k : ℝ) + 2)))
  have h := hc.add log_bits_over_primeBase_tendsto_zero
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [] with n
  rw [Real.log_mul (by positivity : (16 * ((k : ℝ) + 2)) ≠ 0)
    (by positivity : (inputBits n + 1 : ℝ) ≠ 0)]
  simp only [Pi.inv_apply, add_div]
  ring
end ThreeSum.Scales
