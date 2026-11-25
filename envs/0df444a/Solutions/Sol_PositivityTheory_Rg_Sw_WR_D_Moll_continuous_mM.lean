-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.continuous_mM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:28.814651+00:00
-- url     : https://prove2.me/submissions/b2ccd226-b009-4c0d-bd5e-bfaca65fc2f9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollIdA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollId
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_continuous_gK
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_gK_nonneg
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_integrable_gK


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
theorem _root_.solution (ψ : E n → ℂ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (hψ : Continuous ψ) (l : ℝ) :
    Continuous (mM ψ l) := by
  unfold mM
  refine continuous_of_dominated (bound := fun v => B * gK (n := n) v) ?_ ?_ (integrable_gK.const_mul B) ?_
  · intro w
    exact ((by fun_prop : Continuous fun v : E n => ψ (w - l⁻¹ • v)).mul
      (Complex.continuous_ofReal.comp continuous_gK)).aestronglyMeasurable
  · intro w; refine Eventually.of_forall fun v => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gK_nonneg v)]
    exact mul_le_mul_of_nonneg_right (hB _) (gK_nonneg v)
  · exact Eventually.of_forall fun v => (by fun_prop : Continuous fun w : E n => ψ (w - l⁻¹ • v) * (gK v : ℂ))
end PositivityTheory.Rg.Sw.WR.D.Moll
