-- Prove2me | solution 1 for ThreeSum.Scales.primeBase_log_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:28:38.713185+00:00
-- url     : https://prove2.me/submissions/c7994ce7-b2a5-432b-9470-f6185281143d

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
import Theorems.Thm_ThreeSum_Scales_primeWindow_tendsto_atTop

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (4 * primeWindow n : ℝ)) atTop atTop := by
  have hy := (tendsto_natCast_atTop_atTop (R := ℝ)).comp primeWindow_tendsto_atTop
  exact Real.tendsto_log_atTop.comp (hy.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
end ThreeSum.Scales
