-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.analyticAt_ins
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:43.851939+00:00
-- url     : https://prove2.me/submissions/9f7f64e5-4048-4ec9-8ab5-b399f149cf80

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Topology Filter Set
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
variable {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
theorem _root_.solution {e : ℕ} (i : Fin (e + 1)) (z : Fin e → ℂ) :
    AnalyticAt ℂ (fun z' : Fin e → ℂ => Fin.insertNth (α := fun _ => ℂ) i 0 z') z := by
  rw [analyticAt_pi_iff]
  intro j
  by_cases hj : j = i
  · subst hj
    simp only [Fin.insertNth_apply_same]
    exact analyticAt_const
  · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
    simp only [Fin.insertNth_apply_succAbove]
    exact analyticAt_pi_iff.1 analyticAt_id j'
end ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
