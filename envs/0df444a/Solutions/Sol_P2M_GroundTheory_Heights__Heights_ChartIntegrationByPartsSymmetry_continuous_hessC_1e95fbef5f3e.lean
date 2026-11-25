-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_continuous_hessC_1e95fbef5f3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:58:18.536861+00:00
-- url     : https://prove2.me/submissions/4750ef2b-49e6-412c-9a93-3ac50a21ae65

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
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
theorem _root_.solution {φ : (Fin D → ℂ) → ℝ} (hφ : ContDiff ℝ 2 φ) : Continuous (hessC φ) := by
  have h1 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hH : ∀ a b : Fin D → ℂ, Continuous fun z => fderiv ℝ (fderiv ℝ φ) z a b := fun a b =>
    (h1.clm_apply continuous_const).clm_apply continuous_const
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact ((Complex.continuous_ofReal.comp ((hH _ _).add (hH _ _))).add
    (continuous_const.mul (Complex.continuous_ofReal.comp ((hH _ _).sub (hH _ _))))).div_const _
end GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
