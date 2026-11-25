-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.dg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:06:53.997897+00:00
-- url     : https://prove2.me/submissions/31d8986d-45c1-43cd-bf20-e7097a1aa58d

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow
import Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_eq_sum

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
theorem _root_.solution (h : I → ℝ) : dg ι h = ∑ w, ∑ a, (h a : ℂ) • un w a a := by
  conv_lhs => rw [eq_sum (dg ι h)]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a] <;> simp +contextual [dg, Matrix.diagonal_apply, eq_comm]
end PositivityTheory.ThKG.CayleyTransformDarboux
