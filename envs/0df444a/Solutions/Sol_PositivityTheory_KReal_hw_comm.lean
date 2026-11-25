-- Prove2me | solution 1 for PositivityTheory.KReal.hw_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:38:48.73154+00:00
-- url     : https://prove2.me/submissions/01d2d1fc-7d0b-48a4-8e59-a24d967ab505

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Theorems.Thm_PositivityTheory_KReal_sb_symm
import Theorems.Thm_PositivityTheory_KReal_sb_of_pos

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
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : Ix r s → Ix r s → Module.End ℂ M}
    (hρ : GlK ρ) {μ : Ix r s → ℚ} {f : M} (hf : HwK ρ μ f) {a b : Ix r s} (hab : posC a b) :
    ρ a b (ρ b a f) = ((μ a - μ b : ℚ) : ℂ) • f := by
  have h := LinearMap.congr_fun (hρ a b b a (sb_of_pos hab) (sb_symm (sb_of_pos hab))) f
  simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply, hf.2 a b hab, map_zero, sub_zero,
    hf.1] at h
  rw [h, ← sub_smul]
  push_cast
  rfl
end PositivityTheory.KReal
