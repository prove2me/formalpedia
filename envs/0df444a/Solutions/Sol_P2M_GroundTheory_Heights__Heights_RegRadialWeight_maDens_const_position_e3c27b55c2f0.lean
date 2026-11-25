-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegRadialWeight_maDens_const_position_e3c27b55c2f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:43:02.902415+00:00
-- url     : https://prove2.me/submissions/441de5ad-79cd-49bc-b5da-8961ce34597b

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegRadialWeight_hessC_const_9ad8a3d7caf1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMassCompact_mdisc_coord_zero_b76457691cde


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
theorem _root_.solution {m : ℕ} (c : ℝ) (φ : Fin m → (Fin n → ℂ) → ℝ)
    (s : (Fin (m + 1) → ℂ) → Fin n → ℂ) (y : Fin (m + 1) → ℂ) :
    maDens (fun k => (vecCons (fun _ => c) φ : Fin (m + 1) → (Fin n → ℂ) → ℝ) k ∘ s) y = 0 := by
  unfold maDens
  rw [ChartMassCompact.mdisc_coord_zero _ 0 (hessC_const c y)]
  simp
end GroundTheory.Heights₂.Heights.RegRadialWeight
