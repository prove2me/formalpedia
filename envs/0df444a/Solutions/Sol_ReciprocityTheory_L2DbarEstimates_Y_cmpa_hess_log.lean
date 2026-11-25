-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:17:32.030908+00:00
-- url     : https://prove2.me/submissions/0208d3ce-9b29-4e6c-9f9c-6a10027f3032

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaFderivCompApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaCHessComp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_cmpa_wdb_log
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
namespace ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}
private theorem wd_conj_of_complex_differentiableAt_eq_zero {h : V n → ℂ} {y : V n} (hh : DifferentiableAt ℂ h y) (j : Fin n) :
    wd n j (fun v => (starRingEnd ℂ) (h v)) y = 0 := by
  have H := (hh.hasFDerivAt.restrictScalars ℝ).star
  have H2 : fderiv ℝ (fun v => (starRingEnd ℂ) (h v)) y =
      ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp ((fderiv ℂ h y).restrictScalars ℝ) := H.fderiv
  simp only [wd, H2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    map_smul, smul_eq_mul, ContinuousLinearEquiv.coe_coe, starL'_apply, star_mul', Complex.star_def,
    Complex.conj_I]
  ring_nf
  try simp only [Complex.I_sq]
  try ring
end
end ReciprocityTheory.L2DbarEstimates.Y
end

set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {g : V n → ℂ} {x : V n} {U : Set (V n)} (hU : IsOpen U) (hxU : x ∈ U)
    (hg : DifferentiableOn ℂ g U) (hne : ∀ v ∈ U, g v ≠ 0) (j k : Fin n) :
    wd n j (wdb n k (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ))) x = 0 := by
  have hgs : ContDiffOn ℂ ∞ g U := contDiffOn_of_differentiableOn n g U hU hg
  have ev : wdb n k (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun v => conj (fderiv ℂ g v (bas n k) / g v) := by
    filter_upwards [hU.mem_nhds hxU] with v hv
    exact cmpa_wdb_log ((contDiffOn_infty.1 hgs 2).contDiffAt (hU.mem_nhds hv)) (hne v hv) k
  have e1 : wd n j (wdb n k (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ))) x =
      wd n j (fun v => conj (fderiv ℂ g v (bas n k) / g v)) x := by
    simp only [wd, ev.fderiv_eq]
  rw [e1]
  apply wd_conj_of_complex_differentiableAt_eq_zero
  have hD : ContDiffOn ℂ ∞ (fderiv ℂ g) U := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hgs).2
  have h1 := (((hD.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)).clm_apply
    (differentiableAt_const (bas n k))).mul ((hg.differentiableAt (hU.mem_nhds hxU)).inv (hne x hxU))
  exact h1
end ReciprocityTheory.L2DbarEstimates.Y
