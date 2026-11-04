-- Prove2me | solution 1 for ThreeSum.Scales.natSqrt_ratio_tendsto_zero_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:44:36.586633+00:00
-- url     : https://prove2.me/submissions/eb0881a7-d986-4ed6-8407-3227a00e984c

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
import Theorems.Thm_ThreeSum_Scales_natSqrt_tendsto_atTop

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution :
    Tendsto (fun m : ℕ => (Nat.sqrt m : ℝ) / m) atTop (𝓝 0) := by
  have hinv := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp natSqrt_tendsto_atTop).inv_tendsto_atTop
  apply squeeze_zero' _ _ hinv
  · exact Filter.Eventually.of_forall (fun m => by positivity)
  · filter_upwards [natSqrt_tendsto_atTop.eventually (eventually_ge_atTop 1)] with m hm
    have hx : (0 : ℝ) < Nat.sqrt m := by exact_mod_cast (by omega : 0 < Nat.sqrt m)
    have hs : (Nat.sqrt m : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast Nat.sqrt_le' m
    have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hs
    apply (div_le_iff₀ hmpos).mpr
    change (Nat.sqrt m : ℝ) ≤ (Nat.sqrt m : ℝ)⁻¹ * m
    rw [mul_comm ((Nat.sqrt m : ℝ)⁻¹) (m : ℝ)]
    change (Nat.sqrt m : ℝ) ≤ (m : ℝ) / Nat.sqrt m
    apply (le_div_iff₀ hx).mpr
    nlinarith [hs]
end ThreeSum.Scales
