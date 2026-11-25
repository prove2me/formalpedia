-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VarMassNearSmall_abs_sheetSum_le_e119edd687e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:22:51.068687+00:00
-- url     : https://prove2.me/submissions/3beaa7dd-b3fd-408f-a269-dbfc7a48e253

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarMassNearSmall

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal NNReal
noncomputable section
open GroundTheory.Heights₂.Heights.VarMassNearSmall
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.VarMassNearSmall
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ} (hFG : ∀ x s, |F x s| ≤ G x s)
    {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    |sheetSum J A F y| ≤ sheetSum J A G y := by
  classical
  unfold sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  split_ifs with h
  · exact hFG x _
  · simp
end GroundTheory.Heights₂.Heights.VarMassNearSmall
