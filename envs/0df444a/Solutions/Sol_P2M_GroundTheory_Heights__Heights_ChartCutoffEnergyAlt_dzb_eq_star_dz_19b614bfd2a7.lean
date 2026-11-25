-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_dzb_eq_star_dz_19b614bfd2a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:30.247907+00:00
-- url     : https://prove2.me/submissions/b4369995-9bb7-478c-9555-74c7f90ec9d3

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_fderiv_cplx_5349c035cb13

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
open ReciprocityTheory.AnForm.A
namespace GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
theorem _root_.solution {D : ℕ} {v : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hv : DifferentiableAt ℝ v z)
    (j : Fin D) : dzb j (cplx v) z = star (dz j (cplx v) z) := by
  simp only [dz, dzb, fderiv_cplx hv]
  apply Complex.ext <;> simp
end GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
