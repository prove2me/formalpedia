-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_hessC_sub_2ceea7e5a053
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:35:59.784873+00:00
-- url     : https://prove2.me/submissions/273e6d03-e72c-46e6-aeca-e6483316669f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
theorem _root_.solution {D : ℕ} {f g : (Fin D → ℂ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (z : Fin D → ℂ) :
    hessC (fun y => f y - g y) z = hessC f z - hessC g z := by
  have h1 : fderiv ℝ (fun y => f y - g y) = fun y => fderiv ℝ f y - fderiv ℝ g y := by
    funext y
    exact fderiv_sub (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y)
  have hf1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hg1 : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h2 : fderiv ℝ (fderiv ℝ fun y => f y - g y) z = fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ g) z := by
    rw [h1]
    exact fderiv_sub (hf1 z) (hg1 z)
  ext i j
  simp only [hessC, h2, _root_.sub_apply, Matrix.sub_apply]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
