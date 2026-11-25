-- Prove2me | solution 1 for PositivityTheory.KReal.low_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:14:33.381132+00:00
-- url     : https://prove2.me/submissions/092d4f3a-4d0b-420b-b996-fe34caf10885

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
    (hadj : AdjK ρ) (hρ : GlK ρ) {μ : Ix r s → ℚ} {f : A} (hf : HwK ρ μ f) {a b : Ix r s} (hab : posC a b)
    (hμ : μ a = μ b) : ρ b a f = 0 := by
  have h := norm_low hadj hρ hf hab
  rw [hμ] at h
  simpa using h
end PositivityTheory.KReal
