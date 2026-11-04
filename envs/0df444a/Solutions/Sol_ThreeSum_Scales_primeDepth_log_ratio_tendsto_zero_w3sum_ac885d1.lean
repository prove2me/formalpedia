-- Prove2me | solution 1 for ThreeSum.Scales.primeDepth_log_ratio_tendsto_zero_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:48:43.126202+00:00
-- url     : https://prove2.me/submissions/19d0a13c-888c-400e-9572-18fc8b8ed976

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
import Theorems.Thm_ThreeSum_Scales_primeWindow_ge_two
import Theorems.Thm_ThreeSum_Scales_radix_log_ratio_tendsto
import Theorems.Thm_ThreeSum_Scales_radix_eventually_ge_four
import Theorems.Thm_ThreeSum_Scales_primeDepth_log_bound
import Theorems.Thm_ThreeSum_Scales_primeBase_log_tendsto_atTop
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
    Tendsto (fun n : ℕ => (primeDepth radix n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have hupper := radix_log_ratio_tendsto.mul primeBase_log_tendsto_atTop.inv_tendsto_atTop
  simp only [mul_zero] at hupper
  apply squeeze_zero' _ _ hupper
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hn))
  · filter_upwards [radix_eventually_ge_four, eventually_ge_atTop (2 : ℕ)] with n hR hn
    have hy := primeWindow_ge_two n
    have hb : (0 : ℝ) < Real.log (4 * primeWindow n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < 4 * primeWindow n))
    have hlog : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hdepth := (le_div_iff₀ hb).mpr (primeDepth_log_bound hR)
    have hd := div_le_div_of_nonneg_right hdepth hlog.le
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Pi.inv_apply] using hd
end ThreeSum.Scales
