-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RegChartData_one_le_log_growth_6e7711f043a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:27.519328+00:00
-- url     : https://prove2.me/submissions/4c2d83e0-8570-4f66-ac9d-0e7a70c9b2a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PTruncPsh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Set
open ReciprocityTheory.AnForm.A (IsPsh coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RegChartData
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (R : RegChartData A)
namespace GroundTheory.Heights₂.Heights.Regular.RegChartData
theorem _root_.solution (j : Fin R.N) {y : Fin D → ℂ} (hyt : y ∈ (R.chart j).target) :
    1 ≤ Real.log (Real.exp 1 + ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹) := by
  have hy1 : ‖y‖ < 1 := by simpa using R.target_subset j hyt
  have hs : 0 ≤ ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹ := Finset.sum_nonneg fun i _ => by
    rw [Real.log_inv]
    exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) ((norm_le_pi_norm y i).trans hy1.le))
  have := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hs (a := Real.exp 1))
  rwa [Real.log_exp] at this
end GroundTheory.Heights₂.Heights.Regular.RegChartData
