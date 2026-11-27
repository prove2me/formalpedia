-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.ratio_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:23:12.043059+00:00
-- url     : https://prove2.me/submissions/d4e0ae38-aa42-4f73-ba29-706e86794094

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
import Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_pairDet_smul
import Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_pairNorm_smul

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
theorem _root_.solution (u v : ℂ × ℂ) {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) :
    ‖det2 (c • u) (d • v)‖ / (nrm2 (c • u) * nrm2 (d • v)) = ‖det2 u v‖ / (nrm2 u * nrm2 v) := by
  rw [pairDet_smul, pairNorm_smul, pairNorm_smul, norm_mul, norm_mul]
  rw [show ‖c‖ * nrm2 u * (‖d‖ * nrm2 v) = (‖c‖ * ‖d‖) * (nrm2 u * nrm2 v) by ring,
    mul_div_mul_left _ _ (mul_ne_zero (norm_ne_zero_iff.2 hc) (norm_ne_zero_iff.2 hd))]
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
