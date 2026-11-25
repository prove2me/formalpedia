-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.cmpa_wdb_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:25:35.914491+00:00
-- url     : https://prove2.me/submissions/673d3423-ddb5-4427-98d7-e5a9a135fc61

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaFderivCompApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaCHessComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {g : V n → ℂ} {y : V n} (hg : ContDiffAt ℂ 2 g y) (hy : g y ≠ 0) (k : Fin n) :
    wdb n k (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ)) y = conj (fderiv ℂ g y (bas n k) / g y) := by
  have hgd : DifferentiableAt ℂ g y := hg.differentiableAt (by simp)
  have hgR : HasFDerivAt g ((fderiv ℂ g y).restrictScalars ℝ) y := hgd.hasFDerivAt.restrictScalars ℝ
  have hN := hgR.norm_sq
  have hpos : ‖g y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hy)
  have hL := hN.log hpos
  have hF := Complex.ofRealCLM.hasFDerivAt.comp y hL
  unfold wdb
  rw [show (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ)) =
    ⇑Complex.ofRealCLM ∘ fun v => Real.log (‖g v‖ ^ 2) from rfl, hF.fderiv]
  have hG : (g y).re * (g y).re + (g y).im * (g y).im ≠ 0 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm]; exact hpos
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul, innerSL_apply_apply, Complex.ofRealCLM_apply,
    smul_eq_mul, nsmul_eq_mul, Complex.inner, Complex.sq_norm, Complex.normSq_apply]
  apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq_apply] <;>
    field_simp <;>
    ring
end ReciprocityTheory.L2DbarEstimates.Y
