-- Prove2me | solution 1 for PositivityTheory.KReal.norm_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:58:37.211594+00:00
-- url     : https://prove2.me/submissions/71667f94-7b46-4e6c-9e98-350d9df3e477

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Theorems.Thm_PositivityTheory_KReal_sb_symm
import Theorems.Thm_PositivityTheory_KReal_sb_of_pos
import Theorems.Thm_PositivityTheory_KReal_hw_comm

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
theorem _root_.solution {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    {ρ : Ix r s → Ix r s → Module.End ℂ A} (hadj : AdjK ρ) (hρ : GlK ρ) {μ : Ix r s → ℚ} {f : A}
    (hf : HwK ρ μ f) {a b : Ix r s} (hab : posC a b) :
    ‖ρ b a f‖ ^ 2 = ((μ a - μ b : ℚ) : ℝ) * ‖f‖ ^ 2 := by
  have h := hadj b a (sb_symm (sb_of_pos hab)) f (ρ b a f)
  rw [hw_comm hρ hf hab, inner_smul_right, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ((‖ρ b a f‖ ^ 2 : ℝ) : ℂ) = ((((μ a - μ b : ℚ) : ℝ) * ‖f‖ ^ 2 : ℝ) : ℂ) := by
    push_cast at h ⊢
    exact h
  exact_mod_cast h2
end PositivityTheory.KReal
