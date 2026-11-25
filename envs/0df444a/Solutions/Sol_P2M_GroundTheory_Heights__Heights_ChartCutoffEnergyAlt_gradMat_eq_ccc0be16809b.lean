-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_gradMat_eq_ccc0be16809b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:11:33.990024+00:00
-- url     : https://prove2.me/submissions/3c29138f-cfdf-48a7-a787-1b3e7e40769a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_dzb_eq_star_dz_19b614bfd2a7

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
theorem _root_.solution {D : ℕ} {v : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hv : DifferentiableAt ℝ v z) :
    gradMat v v z = vecMulVec (fun j => dz j (cplx v) z) (star fun j => dz j (cplx v) z) := by
  ext j k
  simp only [gradMat, vecMulVec_apply, Pi.star_apply, dzb_eq_star_dz hv]
end GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
