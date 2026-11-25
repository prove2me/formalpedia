-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.lim_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:36.474421+00:00
-- url     : https://prove2.me/submissions/521908a2-73e2-45f6-b918-fd6419368f72

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ExpCombine
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_StepB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_StepC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousCexpIp
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_continuous_mM
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_norm_mM_le
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_tendsto_mM


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
set_option maxHeartbeats 1000000
namespace PositivityTheory.Rg.Sw.WR.D.Moll
theorem _root_.solution (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (ψ : E n → ℂ)
    (hψc : Continuous ψ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (l : ℕ → ℝ) (hl : Tendsto (fun k => (l k)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, Ψ x * mM ψ (l k) (qq x) ∂μ) atTop (𝓝 (∫ x, ψ (qq x) * Ψ x ∂μ)) := by
  have hlim : ∫ x, ψ (qq x) * Ψ x ∂μ = ∫ x, Ψ x * ψ (qq x) ∂μ := by simp_rw [mul_comm]
  rw [hlim]
  refine tendsto_integral_of_dominated_convergence (fun x => ‖Ψ x‖ * B) ?_ (hΨ.norm.mul_const _) ?_ ?_
  · intro k
    exact hΨ.aestronglyMeasurable.mul ((continuous_mM ψ B hB hψc (l k)).measurable.comp hqq).aestronglyMeasurable
  · intro k; refine Eventually.of_forall fun x => ?_
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_mM_le ψ B hB hψc _ _) (norm_nonneg _)
  · exact Eventually.of_forall fun x => tendsto_const_nhds.mul (tendsto_mM ψ B hB hψc l hl (qq x))
end PositivityTheory.Rg.Sw.WR.D.Moll
