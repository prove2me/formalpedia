-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.tmax_eq_of_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:50.596673+00:00
-- url     : https://prove2.me/submissions/94763878-9581-40e9-9ed6-fbbe77262a23

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {a b : ι → ℝ} {j k : ι} (hkj : k ≠ j) (hab : ∀ i, i ≠ j → a i = b i)
    (ha : a j ≤ a k) (hb : b j ≤ b k) : tmax a = tmax b := by
  have key : ∀ {a b : ι → ℝ}, (∀ i, i ≠ j → a i = b i) → a j ≤ a k → tmax a ≤ tmax b := by
    intro a b hab ha
    refine tmax_le fun i => ?_
    by_cases hi : i = j
    · rw [hi]
      calc a j ≤ a k := ha
        _ = b k := hab k hkj
        _ ≤ tmax b := le_tmax b k
    · rw [hab i hi]
      exact le_tmax b i
  exact le_antisymm (key hab ha) (key (fun i hi => (hab i hi).symm) hb)
end ReciprocityTheory.AnForm.A
