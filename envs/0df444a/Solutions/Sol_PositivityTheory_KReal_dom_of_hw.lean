-- Prove2me | solution 1 for PositivityTheory.KReal.dom_of_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:13:30.148538+00:00
-- url     : https://prove2.me/submissions/fa29040f-cced-40b0-8e0b-d31293f52d9f

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Theorems.Thm_PositivityTheory_KReal_norm_low

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] {ρ : Ix r s → Ix r s → Module.End ℂ A}
    (hadj : AdjK ρ) (hρ : GlK ρ) {μ : Ix r s → ℚ} {f : A} (hf : HwK ρ μ f) (h0 : f ≠ 0) : Dom μ := by
  intro a b hab
  have h := norm_low hadj hρ hf hab
  have hp : 0 < ‖f‖ ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ ((μ a - μ b : ℚ) : ℝ) * ‖f‖ ^ 2 := h ▸ sq_nonneg _
  have h3 : (0 : ℝ) ≤ ((μ a - μ b : ℚ) : ℝ) := nonneg_of_mul_nonneg_left h2 hp
  have h4 : (0 : ℚ) ≤ μ a - μ b := by exact_mod_cast h3
  linarith
end PositivityTheory.KReal
