-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.pairNorm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:30:20.873899+00:00
-- url     : https://prove2.me/submissions/98639779-2bc6-45dc-b49c-64f9db21020f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open OnePoint
noncomputable section
open ReciprocityTheory.AnForm.M.CompatibleChartOperations
namespace ReciprocityTheory.AnForm.M.CompatibleChartOperations
theorem _root_.solution (c : ℂ) (u : ℂ × ℂ) : nrm2 (c • u) = ‖c‖ * nrm2 u := by
  simp only [nrm2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, norm_mul, mul_pow]
  rw [← mul_add, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
