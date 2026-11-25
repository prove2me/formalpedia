-- Prove2me | solution 1 for PositivityTheory.KReal.Harm.rename_first_lowering
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:39.091817+00:00
-- url     : https://prove2.me/submissions/65eb5022-20ea-412f-8c4d-ba90748801ee

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
import Theorems.Thm_PI_FockOneDegW_RedOps_lowOp_apply
import Theorems.Thm_PI_FockOneDegW_Swap_linePos_sw
import Theorems.Thm_PI_FockOneDegW_Swap_rename_pderiv


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
open PositivityTheory.KReal.Harm
variable {p q r s : ℕ}
open PI.FockOneDegW.Swap
namespace PositivityTheory.KReal.Harm
theorem _root_.solution (a b : Ix p q) (P : Pol p q r s) :
    rename (sw p q r s) (low1 a b P) =
      PI.FockOneDegW.lowOp (p := r) (q := s) a b (rename (sw p q r s) P) := by
  rw [PI.FockOneDegW.RedOps.lowOp_apply]
  unfold low1
  rw [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hl : linePos ((c, b) : Ln r s p q) = linePos ((b, c) : Ln p q r s) := linePos_sw (b, c)
  rw [hl]
  split_ifs
  · change rename (sw p q r s) (pderiv (a, c) (pderiv (b, c) P)) = _
    rw [rename_pderiv, rename_pderiv]
    rfl
  · simp
end PositivityTheory.KReal.Harm
