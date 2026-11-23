-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_cd_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:27.163409+00:00
-- url     : https://prove2.me/submissions/48b4e04a-ff92-4b16-97b1-20cc9855a2e1

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
theorem _root_.solution {f g : E → Matrix (Fin n) (Fin n) ℂ} (hf : ContDiffOn ℝ k f s)
    (hg : ContDiffOn ℝ k g s) : ContDiffOn ℝ k (fun x => f x * g x) s := by
  rw [slm_cd_iff] at hf hg ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun l _ => (hf i l).mul (hg l j)
end ReciprocityTheory.ChartRestriction.DS
