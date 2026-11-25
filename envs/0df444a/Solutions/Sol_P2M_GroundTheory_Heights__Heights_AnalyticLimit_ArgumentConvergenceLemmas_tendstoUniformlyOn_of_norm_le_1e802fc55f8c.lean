-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_tendstoUniformlyOn_of_norm_le_1e802fc55f8c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:55:42.199127+00:00
-- url     : https://prove2.me/submissions/6678523a-ee99-44e7-a236-4aa081df0e3b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_NormIteratedFDerivCompLeOfIsOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
open Filter Topology Metric Set MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (errE errorWithLinear ell)
noncomputable section
namespace GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
theorem _root_.solution {Y α : Type*} [SeminormedAddCommGroup α] {F : ℝ → Y → α}
    {f : Y → α} {K : Set Y} {β : ℝ → ℝ} (hβ : Tendsto β (𝓝[>] 0) (𝓝 0))
    (h : ∀ᶠ t in 𝓝[>] 0, ∀ y ∈ K, ‖F t y - f y‖ ≤ β t) :
    TendstoUniformlyOn F f (𝓝[>] 0) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  filter_upwards [h, hβ.eventually (gt_mem_nhds he)] with t ht hβt y hy
  rw [dist_comm, dist_eq_norm]
  exact (ht y hy).trans_lt hβt
end GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
