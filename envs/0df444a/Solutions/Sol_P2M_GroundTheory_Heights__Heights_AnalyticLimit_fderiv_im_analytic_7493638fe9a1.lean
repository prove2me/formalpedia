-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_im_analytic_7493638fe9a1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:34.30669+00:00
-- url     : https://prove2.me/submissions/54098d93-bef6-4cfa-ae82-412da00caa04

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PGreenMassReplaceLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_re_analytic_f165eb17d640
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_im_eq_re_mul_254c7de5cbad
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul levi_re_analytic)
noncomputable section
variable {ι : Type} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (v : ι → ℂ) :
    fderiv ℝ (fun z => (S z).im) y v = (fderiv ℂ S y v).im := by
  have hS2 : AnalyticAt ℂ (fun z => -Complex.I * S z) y := analyticAt_const.mul hS
  have h1 : (fun z => (S z).im) = fun z => (-Complex.I * S z).re := funext fun z => im_eq_re_mul _
  rw [h1, fderiv_re_analytic hS2, fderiv_const_mul hS.differentiableAt]
  simp [Complex.mul_re]
end GroundTheory.Heights₂.Heights.AnalyticLimit
