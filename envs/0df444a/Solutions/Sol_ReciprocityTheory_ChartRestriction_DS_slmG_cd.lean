-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slmG_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:37:08.849232+00:00
-- url     : https://prove2.me/submissions/5f4a478b-ea87-42f3-8594-07ca941ba366

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_le_inf

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
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {V : Set X} (hV : IsOpen V) {γ : X → Y} (hγ : ContDiffOn ℝ ∞ γ V)
    (C : ι → Y →L[ℝ] ℝ) {N : ℕ} {w : ι → X → E} (hw : ∀ i, ContDiffOn ℝ N (w i) V) :
    ContDiffOn ℝ N (fun q => slmG C (fderiv ℝ γ q) (fun i => w i q)) V := by
  have hfd : ContDiffOn ℝ N (fun q => fderiv ℝ γ q) V := hγ.fderiv_of_isOpen hV (slm_le_inf N)
  unfold slmG
  first
  | exact ContDiffOn.sum fun i _ => (contDiffOn_const.clm_comp hfd).smulRight (hw i)
  | exact ContDiffOn.fun_sum fun i _ => (contDiffOn_const.clm_comp hfd).smulRight (hw i)
  | simp only [ContinuousLinearMap.sum_apply]
    exact ContDiffOn.sum fun i _ => (contDiffOn_const.clm_comp hfd).smulRight (hw i)
end ReciprocityTheory.ChartRestriction.DS
