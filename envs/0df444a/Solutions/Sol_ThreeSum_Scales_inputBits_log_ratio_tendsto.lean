-- Prove2me | solution 1 for ThreeSum.Scales.inputBits_log_ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:21:15.739401+00:00
-- url     : https://prove2.me/submissions/f2db6560-4eef-45dc-a68c-0654ac0f67aa

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
import Theorems.Thm_ThreeSum_Scales_inputBits_eq_floor
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution :
    Tendsto (fun n : ℕ => (inputBits n : ℝ) / Real.log n) atTop
      (𝓝 (1 / Real.log 2)) := by
  have h := tendsto_nat_floor_div_atTop.comp
    ((Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  have h' := h.div_const (Real.log 2)
  convert h' using 1
  funext n
  simp only [Function.comp_def, ← inputBits_eq_floor]
  rw [Real.logb, div_div, div_mul_cancel₀ _ Parameters.log_two_pos.ne']
end ThreeSum.Scales
