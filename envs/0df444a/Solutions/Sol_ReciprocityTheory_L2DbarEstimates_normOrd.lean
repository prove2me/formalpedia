-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.normOrd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:28:11.102069+00:00
-- url     : https://prove2.me/submissions/d6f70c2e-f697-44a1-bdc3-0cb2cfcd3539

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_HoloSectionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_NormOrd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bound_of_iteratedFDeriv_eq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution : NormOrdStatement.{u} := by
  intro n M _ z f x m hz hf hv
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have hzx : z x ∈ e.target := by rw [he hx]; exact e.map_source hx
  obtain ⟨C, hC⟩ := Y.bound_of_iteratedFDeriv_eq_zero (f ∘ e.symm) e.target (z x)
    e.open_target hzx (hf e he) m (hv e he hx)
  have h1 : ∀ᶠ y in 𝓝 x, ‖(f ∘ e.symm) (z y)‖ ≤ C * ‖z y - z x‖ ^ (m + 1) :=
    hz.continuous.continuousAt.tendsto.eventually hC
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ e.source := e.open_source.mem_nhds hx
  rw [Norm.VanishOrder, Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [h1, h2] with y hy hys
  have hy' : e.symm (z y) = y := by rw [he hys]; exact e.left_inv hys
  simp only [Function.comp_apply, hy'] at hy
  rw [norm_pow, norm_norm]
  exact hy
end ReciprocityTheory.L2DbarEstimates
