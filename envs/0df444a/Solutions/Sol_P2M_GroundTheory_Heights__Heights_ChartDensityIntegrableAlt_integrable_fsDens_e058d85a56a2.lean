-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_integrable_fsDens_e058d85a56a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:08:56.851462+00:00
-- url     : https://prove2.me/submissions/23beb860-15f5-4a99-b214-6ac4b9f24e7c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gaM_lintegral_pi


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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
namespace GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
theorem _root_.solution (D : ℕ) :
    Integrable (fun y : Fin D → ℂ => ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹) := by
  have hcont : Continuous (fun y : Fin D → ℂ => ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) fun y => ?_
    have : 0 < 1 + ∑ i, ‖y i‖ ^ 2 := by positivity
    positivity
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => by
    simp only [Pi.zero_apply]; positivity)]
  have h := gaM_lintegral_pi D 1 one_pos 0
  simp only [add_zero] at h
  rw [h]
  exact ENNReal.ofReal_lt_top
end GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt
