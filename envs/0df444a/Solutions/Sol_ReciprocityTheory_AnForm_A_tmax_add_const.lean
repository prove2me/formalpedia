-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.tmax_add_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:43.376431+00:00
-- url     : https://prove2.me/submissions/23420570-37af-4a26-9301-eafcb133dd05

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_tmax

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
theorem _root_.solution (t : ι → ℝ) (c : ℝ) : tmax (fun j => t j + c) = tmax t + c := by
  apply le_antisymm
  · exact tmax_le fun j => by
      show t j + c ≤ tmax t + c
      linarith [le_tmax t j]
  · obtain ⟨i, hi⟩ := exists_tmax t
    rw [hi]
    exact le_tmax (fun j => t j + c) i
end ReciprocityTheory.AnForm.A
