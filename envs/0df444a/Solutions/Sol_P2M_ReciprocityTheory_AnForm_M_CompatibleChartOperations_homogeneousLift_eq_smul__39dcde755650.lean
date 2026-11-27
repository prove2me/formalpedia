-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_M_CompatibleChartOperations_homogeneousLift_eq_smul__39dcde755650
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:13:33.769161+00:00
-- url     : https://prove2.me/submissions/f6b981f8-f5a5-41a2-888b-6d9e9e57697f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
import Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_homogeneousLift_eq_smul

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
theorem _root_.solution {a a' p : OnePoint ℂ} (h : p ∈ fsPot.U a) (h' : p ∈ fsPot.U a') :
    ∃ c : ℂ, c ≠ 0 ∧ homogeneousLift a p = c • homogeneousLift a' p := by
  obtain ⟨c, hc, e1⟩ := homogeneousLift_eq_smul h
  obtain ⟨c', hc', e2⟩ := homogeneousLift_eq_smul h'
  refine ⟨c / c', div_ne_zero hc hc', ?_⟩
  rw [e1, e2, smul_smul, div_mul_cancel₀ _ hc']
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
