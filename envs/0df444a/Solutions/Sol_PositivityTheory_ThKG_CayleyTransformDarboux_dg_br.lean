-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.dg_br
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:36:34.474352+00:00
-- url     : https://prove2.me/submissions/9eec28fa-efe1-4440-805f-04dc813836ac

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action PositivityTheory.KReal
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.CayleyTransformDarboux
variable {ι I M : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.ThKG.CayleyTransformDarboux
theorem _root_.solution (h : I → ℝ) (w : ι) (a b : I) : dg ι h * un w a b - un w a b * dg ι h = ((h a - h b : ℝ) : ℂ) • un w a b := by
  ext w' c d
  by_cases e : w' = w
  · subst e
    simp only [un, dg, Pi.sub_apply, Pi.mul_apply, Pi.single_eq_same, Matrix.sub_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Pi.smul_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs with h1
    · obtain ⟨rfl, rfl⟩ := h1; push_cast; ring
    · simp
  · simp [un, Pi.single_eq_of_ne e]
end PositivityTheory.ThKG.CayleyTransformDarboux
