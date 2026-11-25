-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_cd_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:01.105173+00:00
-- url     : https://prove2.me/submissions/89cb7d7f-0105-4d63-9547-724c6f430d57

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cd_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cd_det

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
    ContDiffOn ℝ k (fun x => (f x).adjugate) s := by
  rw [slm_cd_iff]
  intro i j
  simp only [Matrix.adjugate_apply]
  apply slm_cd_det
  rw [slm_cd_iff] at hf ⊢
  intro a b
  by_cases h : a = j
  · subst h
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simp only [Matrix.updateRow_ne h]
    exact hf a b
end ReciprocityTheory.ChartRestriction.DS
