-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_eq_zero_of_gradMat_2c7a0b515ee8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:09:41.186517+00:00
-- url     : https://prove2.me/submissions/e6a82f24-6a7e-4cf3-8586-3f9a4d0086ec

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_smul_fst


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
theorem _root_.solution {n : ℕ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} {v w : (Fin (n + 1) → ℂ) → ℝ}
    {z : Fin (n + 1) → ℂ} (h : gradMat v w z = 0) : gradDens φ v w z = 0 := by
  have h0 := mdisc_cons_smul_fst (0 : ℂ) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) fun i => hessC (φ i) z
  simp only [smul_zero, zero_mul] at h0
  simp [gradDens, h, h0]
end GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
