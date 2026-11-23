-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_cd_conjT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:07.556433+00:00
-- url     : https://prove2.me/submissions/49dfa03a-dd71-4245-a7a6-920ba81949c4

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cd_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {k : WithTop ℕ∞}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {f : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ k f s) :
    ContDiffOn ℝ k (fun x => (f x)ᴴ) s := by
  rw [slm_cd_iff] at hf ⊢
  intro i j
  have := (Complex.conjCLE.contDiff (n := k)).comp_contDiffOn (hf j i)
  simpa [Function.comp_def, Matrix.conjTranspose_apply] using this
end ReciprocityTheory.ChartRestriction.DS
