-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_usc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:49:26.199326+00:00
-- url     : https://prove2.me/submissions/3ccaf8ae-4fdf-430a-9a5c-0424f27b90cf

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_add_const
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_mono


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
theorem _root_.solution {X : Type*} [TopologicalSpace X] {U : Set X} (η : ℝ) {u : ι → X → ℝ}
    (hu : ∀ j, UpperSemicontinuousOn (u j) U) :
    UpperSemicontinuousOn (fun z => regMax η (fun j => u j z)) U := by
  intro z hz y hy
  have he : 0 < (y - regMax η (fun j => u j z)) / 2 := by linarith
  have hev : ∀ᶠ x in 𝓝[U] z, ∀ j, u j x < u j z + (y - regMax η (fun j => u j z)) / 2 :=
    Filter.eventually_all.2 fun j => hu j z hz _ (by linarith)
  filter_upwards [hev] with x hx
  calc regMax η (fun j => u j x)
      ≤ regMax η (fun j => u j z + (y - regMax η (fun j => u j z)) / 2) :=
        regMax_mono η fun j => (hx j).le
    _ = regMax η (fun j => u j z) + (y - regMax η (fun j => u j z)) / 2 := regMax_add_const η _ _
    _ < y := by linarith
end ReciprocityTheory.AnForm.A
