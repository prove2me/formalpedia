-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_sq_half_fff74164f88e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:22:58.666149+00:00
-- url     : https://prove2.me/submissions/07d4180f-8fc1-4243-8e3a-f3a4d6233ca0

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.TubeFormComparison
namespace GroundTheory.Heights₂.Heights.TubeFormComparison
theorem _root_.solution {N : ℕ} {v : (Fin N → ℂ) → ℝ} {y : Fin N → ℂ} (hv : ContDiffAt ℝ 2 v y)
    (w : Fin N → ℂ) :
    levi (fun z => v z ^ 2 / 2) y w =
      ((fderiv ℝ v y w) ^ 2 + (fderiv ℝ v y (Complex.I • w)) ^ 2) / 4 + v y * levi v y w := by
  have hD : HasFDerivAt (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v) y) y :=
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hev : fderiv ℝ (fun z => v z ^ 2 / 2) =ᶠ[𝓝 y] fun z => v z • fderiv ℝ v z := by
    filter_upwards [hv.eventually (by simp)] with z hz
    have h1 : HasFDerivAt (fun z => v z ^ 2 / 2) (v z • fderiv ℝ v z) z := by
      have h0 := ((hz.differentiableAt (by norm_num)).hasFDerivAt.pow 2).mul_const (1 / 2 : ℝ)
      have e : (fun z => v z ^ 2 / 2) = fun u => v u ^ 2 * (1 / 2) := funext fun u => by ring
      rw [e]
      refine h0.congr_fderiv ?_
      ext u
      simp
      ring
    exact h1.fderiv
  have hv1 : HasFDerivAt v (fderiv ℝ v y) y := (hv.differentiableAt (by norm_num)).hasFDerivAt
  have hF := ((hv1.smul hD).congr_of_eventuallyEq hev).fderiv
  unfold levi
  rw [hF]
  simp
  ring
end GroundTheory.Heights₂.Heights.TubeFormComparison
