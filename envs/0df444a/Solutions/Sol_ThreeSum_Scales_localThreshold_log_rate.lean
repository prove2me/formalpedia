-- Prove2me | solution 1 for ThreeSum.Scales.localThreshold_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:26:32.450647+00:00
-- url     : https://prove2.me/submissions/58a6a8d7-f513-4205-8dfd-877d85e6ea3e

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
import Theorems.Thm_ThreeSum_Scales_even_output_rate
import Theorems.Thm_ThreeSum_Scales_localThreshold_log_formula

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution :
    Tendsto (fun h : ℕ => Real.log (LocalCoverBounds.localThreshold h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (2 * Parameters.E + 1)) := by
  have hs := even_output_rate.add (tendsto_const_nhds (x := (1 : ℝ)))
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
  have hpos : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  rw [localThreshold_log_formula]
  field_simp
end ThreeSum.Scales
