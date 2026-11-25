-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.kDens_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:41.755703+00:00
-- url     : https://prove2.me/submissions/7f650d0c-ca33-4b3e-8812-45b9e5b196ec

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HasCompactSupportCompHypInclAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : kDens n * (Real.pi / 2 * (1 / ((n : ℝ) + 1))) =
    (n.factorial : ℝ) * (2 / Real.pi) ^ n := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold kDens
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
end ReciprocityTheory.AnForm.A
