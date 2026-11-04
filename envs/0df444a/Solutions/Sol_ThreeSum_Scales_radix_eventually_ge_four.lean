-- Prove2me | solution 1 for ThreeSum.Scales.radix_eventually_ge_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:24.457818+00:00
-- url     : https://prove2.me/submissions/a93366b2-503f-4f2e-8d02-16ea58ff931b

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
import Theorems.Thm_ThreeSum_Scales_radix_pos
import Theorems.Thm_ThreeSum_Scales_radix_log_tendsto_atTop

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution : ∀ᶠ n : ℕ in atTop, 4 ≤ radix n := by
  filter_upwards [radix_log_tendsto_atTop.eventually (eventually_ge_atTop (Real.log 4))] with n hn
  have hr : (0 : ℝ) < radix n := by exact_mod_cast radix_pos n
  have h : (4 : ℝ) ≤ radix n := (Real.log_le_log_iff (by norm_num) hr).mp hn
  exact_mod_cast h
end ThreeSum.Scales
