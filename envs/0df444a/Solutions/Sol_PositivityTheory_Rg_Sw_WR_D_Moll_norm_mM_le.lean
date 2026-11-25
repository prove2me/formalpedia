-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.norm_mM_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:51:06.676835+00:00
-- url     : https://prove2.me/submissions/06b257e6-0b7d-44ee-ab3e-a27123577add

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollIdA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollId
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_gK_nonneg
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_integrable_gK
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_integral_gK


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
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D.Moll
theorem _root_.solution (ψ : E n → ℂ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (hψ : Continuous ψ) (l : ℝ) (w : E n) :
    ‖mM ψ l w‖ ≤ B := by
  unfold mM
  calc ‖∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ)‖ ≤ ∫ v, B * gK (n := n) v := by
        refine norm_integral_le_of_norm_le (integrable_gK.const_mul B) (Eventually.of_forall fun v => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gK_nonneg v)]
        exact mul_le_mul_of_nonneg_right (hB _) (gK_nonneg v)
    _ = B := by rw [integral_const_mul, integral_gK, mul_one]
end PositivityTheory.Rg.Sw.WR.D.Moll
