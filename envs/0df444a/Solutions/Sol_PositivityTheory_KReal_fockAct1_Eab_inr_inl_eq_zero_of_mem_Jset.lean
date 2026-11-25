-- Prove2me | solution 1 for PositivityTheory.KReal.fockAct1_Eab_inr_inl_eq_zero_of_mem_Jset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:48.296255+00:00
-- url     : https://prove2.me/submissions/6ea96b49-adb5-4bae-9ff2-0744b68c78f3

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CorePair
import Theorems.Thm_PI_FJM_jointHarmonicsIffLaplacians
import Theorems.Thm_PI_FJM_leftOffDiagonalActionFormula
import Theorems.Thm_PI_FockOneDegW_Core_pd_comm
import Theorems.Thm_PI_WFJM_jointHarmonicsIffLaplacians
import Theorems.Thm_PI_WFJM_leftOffDiagonalActionFormula


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
namespace PositivityTheory.KReal
theorem _root_.solution {p q r : ℕ} {x : Pol p q r 0} (hx : x ∈ Jset p q r 0) (i : Fin p) (j : Fin q) :
    fockAct1 p q r 0 (Eab (.inr j) (.inl i)) x = 0 := by
  have h := ((PI.FJM.jointHarmonicsIffLaplacians p q r 0 x).1 hx).2.1 i j
  rw [PI.FJM.leftOffDiagonalActionFormula p q r 0 _ _ (by simp)]
  simp only [PI.FJM.rai1, PI.FJM.lapB, PI.FJM.dd, LinearMap.sum_apply, Fintype.sum_sum_type,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero, Module.End.mul_apply, raiB, lowB, linePos] at h ⊢
  simp only [Bool.false_eq_true, if_false, if_true, LinearMap.neg_apply, Finset.sum_neg_distrib, neg_eq_zero]
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => PI.FockOneDegW.Core.pd_comm _ _ _
end PositivityTheory.KReal
