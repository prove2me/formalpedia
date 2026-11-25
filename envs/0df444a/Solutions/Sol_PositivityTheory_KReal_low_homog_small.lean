-- Prove2me | solution 1 for PositivityTheory.KReal.low_homog_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:11:14.520191+00:00
-- url     : https://prove2.me/submissions/28c53fb6-c096-48e1-b2cf-5afe37e92bf6

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
import Theorems.Thm_PositivityTheory_KReal_Harm_hc_ext
import Theorems.Thm_PI_FockOneDegW_RedOps_hc_lowOp


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
open Harm
variable {p q r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution (c d : Ix r s) {e : ℕ} (he : e < 2) {g : Pol p q r s}
    (hg : g ∈ homog (Ix p q × Ix r s) e) : PI.FockOneDegW.lowOp (p := p) (q := q) c d g = 0 := by
  refine hc_ext fun n => ?_
  rw [PI.FockOneDegW.RedOps.hc_lowOp, homogeneousComponent_of_mem hg, if_neg (by omega), map_zero, map_zero]
end PositivityTheory.KReal
