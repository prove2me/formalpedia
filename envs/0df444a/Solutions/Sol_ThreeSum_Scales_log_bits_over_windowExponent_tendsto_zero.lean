-- Prove2me | solution 1 for ThreeSum.Scales.log_bits_over_windowExponent_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:25.484368+00:00
-- url     : https://prove2.me/submissions/ea992774-b2e6-4717-ac91-d2f7c657bad6

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
import Theorems.Thm_ThreeSum_Scales_windowExponent_tendsto_atTop
import Theorems.Thm_ThreeSum_Scales_bits_add_one_le_windowExponent_sq
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
    Tendsto (fun m : ℕ => Real.log (m + 1 : ℝ) / windowExponent m) atTop (𝓝 0) := by
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).comp windowExponent_tendsto_atTop
  have hu := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht).const_mul 2
  simp only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · exact Filter.Eventually.of_forall (fun m =>
      div_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) m; linarith))
        (Nat.cast_nonneg _))
  · filter_upwards [] with m
    have hs : (m + 1 : ℝ) ≤ (windowExponent m : ℝ) ^ 2 := by
      exact_mod_cast bits_add_one_le_windowExponent_sq m
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < m + 1) hs
    rw [Real.log_pow] at hlog
    have hd := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg (α := ℝ) (windowExponent m))
    simpa only [Function.comp_def, id_eq, Nat.cast_ofNat, mul_div_assoc] using hd
end ThreeSum.Scales
