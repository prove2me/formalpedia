-- Prove2me | solution 1 for PositivityTheory.KReal.low_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:32:51.138621+00:00
-- url     : https://prove2.me/submissions/2bcd28fb-9c78-4084-9c73-0946239e8712

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Theorems.Thm_FockRaiseLowInner_fockInner_X_mul
import Theorems.Thm_FockRaiseLowInner_fockInner_neg_right
import Theorems.Thm_PI_FHS_fockInner_X_mul
import Theorems.Thm_PI_FHS_fockInner_neg_right
import Theorems.Thm_PI_FHS_fockInner_pderiv


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
variable {p q r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution (l : Ln p q r s) (P Q : Pol p q r s) :
    fockInner (lowB l P) Q = sgnC l * fockInner P (raiB l Q) := by
  unfold raiB lowB sgnC
  by_cases h : linePos l = true
  · simp only [h, if_true, one_mul]
    exact PI.FHS.fockInner_pderiv l P Q
  · rw [if_neg h, if_neg h, if_neg h, LinearMap.neg_apply, PI.FHS.fockInner_neg_right, neg_one_mul, neg_neg]
    exact PI.FHS.fockInner_X_mul l P Q
end PositivityTheory.KReal
