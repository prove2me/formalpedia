-- Prove2me | solution 1 for ThreeSum.Scales.even_output_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:21:51.599919+00:00
-- url     : https://prove2.me/submissions/fa876595-5c6a-4e91-b50a-30d32b08dcf6

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
import Theorems.Thm_ThreeSum_BinomialEntropy_output_table_rate
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
    Tendsto (fun h : ℕ => Real.log (LocalCoverBounds.outputCount (512 * h) h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (2 * Parameters.E)) := by
  have ht : Tendsto (fun h : ℕ => 2 * h) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with h hh
    omega
  have hr := BinomialEntropy.output_table_rate.comp ht
  convert hr using 1
  funext h
  simp only [Function.comp_def, LocalCoverBounds.outputCount, Nat.cast_mul, Nat.cast_ofNat]
  rw [show 256 * (2 * h) = 512 * h by omega]
end ThreeSum.Scales
