-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_log_norm_pluriharmonic_feca3f777c61
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:57:42.525838+00:00
-- url     : https://prove2.me/submissions/d67a6038-c4c7-45ad-a654-752ba56df206

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegularizedCurvature
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_const_1f6796170df7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
set_option linter.unusedSectionVars false
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
theorem _root_.solution {T : (J → ℂ) → ℂ} {z : J → ℂ} (hT : AnalyticAt ℂ T z) (h0 : T z ≠ 0)
    (w : J → ℂ) : ContDiffAt ℝ 2 (fun y => Real.log ‖T y‖) z ∧
      ReciprocityTheory.AnForm.levi (fun y => Real.log ‖T y‖) z w = 0 := by
  have hG : AnalyticAt ℂ (fun y => Complex.log (T y / T z)) z := by
    refine (hT.div analyticAt_const h0).clog ?_
    show T z / T z ∈ Complex.slitPlane
    rw [div_self h0]
    exact Complex.one_mem_slitPlane
  have hev : (fun y => Real.log ‖T y‖) =ᶠ[𝓝 z]
      fun y => (Complex.log (T y / T z)).re + Real.log ‖T z‖ * (fun _ : J → ℂ => (1 : ℝ)) y := by
    filter_upwards [hT.continuousAt.eventually_ne h0] with y hy
    rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.mpr hy) (norm_ne_zero_iff.mpr h0)]
    ring
  have hre : ContDiffAt ℝ 2 (fun y => (Complex.log (T y / T z)).re) z := by
    have h := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp z (hG.restrictScalars.contDiffAt (n := 2))
    convert h using 1
    funext y
    simp
  have hc : ContDiffAt ℝ 2 (fun _ : J → ℂ => (1 : ℝ)) z := contDiffAt_const
  refine ⟨(hre.add (contDiffAt_const.mul hc)).congr_of_eventuallyEq hev, ?_⟩
  rw [ReciprocityTheory.AnForm.levi_congr hev w, ReciprocityTheory.AnForm.levi_add_smul _ hre hc w,
    ReciprocityTheory.AnForm.levi_re_analytic hG w, levi_const]
  ring
end GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
