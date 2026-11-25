-- Prove2me | solution 1 for PositivityTheory.KReal.Harm.homogComponent_comm_first_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:13.296258+00:00
-- url     : https://prove2.me/submissions/9ec87ef9-011d-4e2a-b4b8-4c2442d6d2d2

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
import Theorems.Thm_PI_FockOneDegW_kernel_highest_weight


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
namespace PositivityTheory.KReal.Harm
theorem _root_.solution {a b : Ix p q} (h : sameBlock a b) (e : ℕ) (P : Pol p q r s) :
    homogeneousComponent e (fockAct1 p q r s (Eab a b) P) =
      fockAct1 p q r s (Eab a b) (homogeneousComponent e P) := by
  exact PI.FockOneDegW.kernel_highest_weight p q r s a b h e P
end PositivityTheory.KReal.Harm
