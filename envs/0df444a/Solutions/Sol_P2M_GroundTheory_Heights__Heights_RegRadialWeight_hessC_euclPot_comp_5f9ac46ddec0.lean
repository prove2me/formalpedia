-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegRadialWeight_hessC_euclPot_comp_5f9ac46ddec0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:40:44.025818+00:00
-- url     : https://prove2.me/submissions/cadbed6d-79bd-4856-8291-cb5cefecf8a3

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOnChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRadialPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffBoundaryBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegRadialWeight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_euclPot_53e03a97724f
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_add_re_analytic


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegRadialWeight
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.RegRadialWeight
theorem _root_.solution {D : ℕ} {s : (Fin D → ℂ) → Fin n → ℂ} {y : Fin D → ℂ} (hs : AnalyticAt ℂ s y)
    (x : Fin n → ℂ) : hessC (euclPot ∘ s) y = hessC (fun w => euclPot (s w - x)) y := by
  have hsC : ContDiffAt ℝ 2 s y := hs.contDiffAt.restrict_scalars ℝ
  have hE : ContDiffAt ℝ 2 (euclPot ∘ s) y :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp y hsC
  have hsj : ∀ j, AnalyticAt ℂ (fun w => s w j) y := analyticAt_pi_iff.1 hs
  have hG : AnalyticAt ℂ (fun w => ∑ j, (-2 * (s w j * (starRingEnd ℂ) (x j)) + (Complex.normSq (x j) : ℂ))) y :=
    Finset.analyticAt_fun_sum _ fun j _ =>
      (analyticAt_const.mul ((hsj j).mul analyticAt_const)).add analyticAt_const
  have heq : (fun w => euclPot (s w - x)) = fun w => (euclPot ∘ s) w +
      (∑ j, (-2 * (s w j * (starRingEnd ℂ) (x j)) + (Complex.normSq (x j) : ℂ))).re := by
    funext w
    simp only [euclPot, Function.comp_apply, Pi.sub_apply, Complex.re_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp [Complex.mul_re]
    ring
  rw [heq, hessC_add_re_analytic _ _ y hE hG]
end GroundTheory.Heights₂.Heights.RegRadialWeight
