-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartDensityIntegrable_proof_2baed358c155
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:33:04.469406+00:00
-- url     : https://prove2.me/submissions/41b52245-989a-4c92-9c1a-bc2cc45e4a6f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_hermChartPot_eq_gbPot_affine_4211beb1f02e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_integrable_fsDens_e058d85a56a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_integrable_comp_affine_04c215816f18
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_maDensity_comp_affine_974c4adc07ab
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_maDensity_gbPot


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
open ChartDensityIntegrableAlt
namespace GroundTheory.Heights₂.Heights
namespace ChartDensityIntegrable
theorem _root_.solution : ChartDensityIntegrable.Statement := by
  intro e M hM
  obtain ⟨c, P, κ, hP, hpot⟩ := hermChartPot_eq_gbPot_affine M hM
  have h : (fun y : Fin e → ℂ => maDensity (fun _ : Fin e => hermChartPot M) y) = fun y =>
      (Complex.normSq P.det * ((e.factorial : ℝ) / Real.pi ^ e)) *
        ((1 + ∑ i, ‖(c + P *ᵥ y) i‖ ^ 2) ^ (e + 1))⁻¹ := by
    funext y
    rw [hpot, ChartMongeAmpereAffineInvariance.maDensity_comp_affine gbPot c P hP κ y, maDensity_gbPot]
    ring
  rw [h]
  exact (integrable_comp_affine (integrable_fsDens e) c P hP).const_mul _
end ChartDensityIntegrable
end GroundTheory.Heights₂.Heights
