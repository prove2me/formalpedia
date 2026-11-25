-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.integrable_fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:14:28.222257+00:00
-- url     : https://prove2.me/submissions/0fa529c6-67b8-4093-b24b-aa382f1d3aaa

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
open ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
namespace ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
theorem _root_.solution {n : ℕ} {f : V n → ℂ} (hf : LocallyIntegrable f volume) {φ : V n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (u : V n) :
    Integrable (fun y => f y * fderiv ℝ φ y u) volume := by
  have h1 : Continuous (fun y => fderiv ℝ φ y u) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact hf.integrable_smul_right_of_hasCompactSupport h1 (hc.fderiv_apply (𝕜 := ℝ) u)
end ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
