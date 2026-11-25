-- Prove2me | solution 1 for PositivityTheory.KReal.rai_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:19.383674+00:00
-- url     : https://prove2.me/submissions/936566c0-f1f6-400c-b30b-8e8f06923765

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Theorems.Thm_FockRaiseLowInner_fockInner_X_mul
import Theorems.Thm_FockRaiseLowInner_fockInner_neg_left
import Theorems.Thm_PI_FHS_fockInner_X_mul
import Theorems.Thm_PI_FHS_fockInner_neg_left
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
    fockInner (raiB l P) Q = sgnC l * fockInner P (lowB l Q) := by
  unfold raiB lowB sgnC
  by_cases h : linePos l = true
  · simp only [h, if_true, one_mul]
    exact PI.FHS.fockInner_X_mul l P Q
  · rw [if_neg h, if_neg h, if_neg h, LinearMap.neg_apply, PI.FHS.fockInner_neg_left, neg_one_mul]
    exact congrArg Neg.neg (PI.FHS.fockInner_pderiv l P Q)
end PositivityTheory.KReal
