-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_one_add_sum_le_ee50fd91baad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:49:00.323443+00:00
-- url     : https://prove2.me/submissions/bf8f6d28-50ee-43b9-b3c9-b48329e85b53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PHodgeDerivative
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_norm_coord_lt_a42ac747c733
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_log_inv_sq_nonneg_b1faa07e0605


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
open Metric Filter Topology Matrix
open GroundTheory.Heights₂.Heights.MCBounds GroundTheory.Heights₂.Heights.MCDet
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
namespace GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
theorem _root_.solution {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ}
    (hz : z ∈ puncturedChart h (ball (0 : Fin n → ℂ) 1)) :
    1 + ∑ i, ‖cuspCoord h z i‖⁻¹ ≤ (1 + a) * Real.exp (chartRadius h z / 2) := by
  have hlt : ∀ j, ‖cuspCoord h z j‖ < 1 := fun j => norm_coord_lt hz.1 _
  have hnn : ∀ j, 0 ≤ Real.log (‖cuspCoord h z j‖ ^ 2)⁻¹ := fun j => log_inv_sq_nonneg (hlt j)
  have hr0 : 0 ≤ chartRadius h z :=
    add_nonneg (Real.exp_pos 1).le (Finset.sum_nonneg fun j _ => hnn j)
  have h1 : 1 ≤ Real.exp (chartRadius h z / 2) := Real.one_le_exp (by linarith)
  have hi : ∀ i, ‖cuspCoord h z i‖⁻¹ ≤ Real.exp (chartRadius h z / 2) := by
    intro i
    have hpos : 0 < ‖cuspCoord h z i‖ := norm_pos_iff.mpr (hz.2 i)
    have e1 : Real.log (‖cuspCoord h z i‖ ^ 2)⁻¹ = 2 * Real.log ‖cuspCoord h z i‖⁻¹ := by
      rw [Real.log_inv, Real.log_inv, Real.log_pow]
      push_cast
      ring
    have hs := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    have hle : Real.log ‖cuspCoord h z i‖⁻¹ ≤ chartRadius h z / 2 := by
      unfold chartRadius
      rw [e1] at hs
      linarith [Real.exp_pos 1]
    calc ‖cuspCoord h z i‖⁻¹ = Real.exp (Real.log ‖cuspCoord h z i‖⁻¹) :=
          (Real.exp_log (inv_pos.mpr hpos)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hle
  have hs : ∑ i, ‖cuspCoord h z i‖⁻¹ ≤ a * Real.exp (chartRadius h z / 2) := by
    calc ∑ i, ‖cuspCoord h z i‖⁻¹ ≤ ∑ _i : Fin a, Real.exp (chartRadius h z / 2) :=
          Finset.sum_le_sum fun i _ => hi i
      _ = a * Real.exp (chartRadius h z / 2) := by simp
  linarith
end GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
