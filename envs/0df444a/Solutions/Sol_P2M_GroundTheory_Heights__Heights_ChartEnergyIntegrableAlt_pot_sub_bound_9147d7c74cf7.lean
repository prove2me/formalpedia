-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_pot_sub_bound_9147d7c74cf7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:48:02.8692+00:00
-- url     : https://prove2.me/submissions/d327bfd5-5593-4272-8b12-f15824733517

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStBA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyIntegrableAlt_quad_pos_39af722e88fa

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyIntegrableAlt
namespace GroundTheory.Heights₂.Heights.ChartEnergyIntegrableAlt
theorem _root_.solution (hCmp : HermFormCompare.Statement) {e : ℕ} {M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ}
    (hM : M.PosDef) (hN : N.PosDef) :
    ∃ K : ℝ, ∀ y : Fin e → ℂ, ‖hermChartPot M y - hermChartPot N y‖ ≤ K := by
  obtain ⟨c, hc, h1⟩ := hCmp _ M N hM hN
  obtain ⟨c', hc', h2⟩ := hCmp _ N M hN hM
  refine ⟨|Real.log c| + |Real.log c'|, fun y => ?_⟩
  have hqM := quad_pos hM y
  have hqN := quad_pos hN y
  have a1 := Real.log_le_log hqM (h1 (Fin.cons 1 y))
  have a2 := Real.log_le_log hqN (h2 (Fin.cons 1 y))
  rw [Real.log_mul hc.ne' hqN.ne'] at a1
  rw [Real.log_mul hc'.ne' hqM.ne'] at a2
  simp only [hermChartPot, Real.log_sqrt hqM.le, Real.log_sqrt hqN.le, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log c), le_abs_self (Real.log c'), abs_nonneg (Real.log c),
    abs_nonneg (Real.log c')]
end GroundTheory.Heights₂.Heights.ChartEnergyIntegrableAlt
