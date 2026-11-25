-- Prove2me | solution 1 for P2M_PositivityTheory_KReal_fockInner_sub_left__b47db5d98c95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:59:19.060829+00:00
-- url     : https://prove2.me/submissions/b3f89cb1-d5f2-43ac-bd07-acaac1808a3b

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreProj
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreNonv
import Theorems.Thm_FockRaiseLowInner_fockInner_add_left
import Theorems.Thm_FockRaiseLowInner_fockInner_neg_left
import Theorems.Thm_PI_FHS_fockInner_add_left
import Theorems.Thm_PI_FHS_fockInner_neg_left


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
theorem _root_.solution (P P' Q : Pol p q r s) :
    fockInner (P - P') Q = fockInner P Q - fockInner P' Q := by
  rw [sub_eq_add_neg, PI.FHS.fockInner_add_left, PI.FHS.fockInner_neg_left, sub_eq_add_neg]
end PositivityTheory.KReal
