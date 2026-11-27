-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.pairDet_homogeneousLift_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:22:49.07548+00:00
-- url     : https://prove2.me/submissions/8ccddeb0-877f-4c4d-9590-f67b2b9198df

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
import Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_homogeneousLift_eq_smul
import Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_pairDet_smul
import Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_pairDet_homogeneousCoord_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open OnePoint
noncomputable section
open ReciprocityTheory.AnForm.M.CompatibleChartOperations
namespace ReciprocityTheory.AnForm.M.CompatibleChartOperations
theorem _root_.solution {a b p q : OnePoint ℂ} (hp : p ∈ fsPot.U a) (hq : q ∈ fsPot.U b)
    (h : det2 (homogeneousLift a p) (homogeneousLift b q) = 0) : p = q := by
  obtain ⟨c, hc, e1⟩ := homogeneousLift_eq_smul hp
  obtain ⟨d, hd, e2⟩ := homogeneousLift_eq_smul hq
  rw [e1, e2, pairDet_smul] at h
  exact pairDet_homogeneousCoord_eq_zero ((mul_eq_zero.1 h).resolve_left (mul_ne_zero hc hd))
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
