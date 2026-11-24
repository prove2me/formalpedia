-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_exp_sub_one_le_bd2115446053
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:30.145232+00:00
-- url     : https://prove2.me/submissions/85b17ae3-855d-49e9-94a4-70adcb87235b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Theta.SecondKind
open GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (x : 𝔸) : ‖NormedSpace.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have hs : Summable (fun n : ℕ => ‖((n.factorial : ℝ)⁻¹) • x ^ n‖) :=
    NormedSpace.norm_expSeries_summable' x
  have hr : Summable (fun n : ℕ => ‖x‖ ^ n / (n.factorial : ℝ)) := Real.summable_pow_div_factorial _
  have he : NormedSpace.exp x = ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • x ^ n := by
    rw [NormedSpace.exp_eq_tsum ℝ]
  have hR : Real.exp ‖x‖ = ∑' n : ℕ, ‖x‖ ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hs1 : Summable (fun n : ℕ => ‖(((n + 1).factorial : ℝ)⁻¹) • x ^ (n + 1)‖) :=
    (summable_nat_add_iff 1).2 hs
  have hr1 : Summable (fun n : ℕ => ‖x‖ ^ (n + 1) / ((n + 1).factorial : ℝ)) :=
    (summable_nat_add_iff 1).2 hr
  rw [he, hR, hs.of_norm.tsum_eq_zero_add, hr.tsum_eq_zero_add]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul, div_one,
    add_sub_cancel_left]
  refine (norm_tsum_le_tsum_norm hs1).trans (hs1.tsum_le_tsum (fun n => ?_) hr1)
  rw [norm_smul, div_eq_inv_mul, Real.norm_of_nonneg (by positivity)]
  gcongr
  exact norm_pow_le' x n.succ_pos
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
