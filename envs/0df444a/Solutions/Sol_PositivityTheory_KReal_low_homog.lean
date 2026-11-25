-- Prove2me | solution 1 for PositivityTheory.KReal.low_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:32.948431+00:00
-- url     : https://prove2.me/submissions/5da3fa15-7134-4234-a7a3-02c0d891ca24

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
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
theorem _root_.solution (c d : Ix r s) {e : ℕ} {g : Pol p q r s} (hg : g ∈ homog (Ix p q × Ix r s) (e + 2)) :
    PI.FockOneDegW.lowOp (p := p) (q := q) c d g ∈ homog (Ix p q × Ix r s) e := by
  have h1 : PI.FockOneDegW.lowOp (p := p) (q := q) c d g =
      homogeneousComponent e (PI.FockOneDegW.lowOp (p := p) (q := q) c d g) := by
    rw [PI.FockOneDegW.RedOps.hc_lowOp, homogeneousComponent_of_mem hg, if_pos rfl]
  rw [h1]
  exact homogeneousComponent_mem _ _
end PositivityTheory.KReal
