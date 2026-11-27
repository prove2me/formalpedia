-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_Gi_sub_one_le_99e04270903b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:13:05.623358+00:00
-- url     : https://prove2.me/submissions/23687045-b164-4e27-8a2f-aeac341cfaff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_exp_sub_one_le_bd2115446053
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_exp_le_cae1f6c984d7
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_one_le_75def0573aee
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_cc_nonneg_87c80e7e3807
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_factor_le_ca1c8d676e83

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
variable (F : OrthoFrame)
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution (y : Fin F.dim → ℝ) (τ : Fin F.f) (k : ℕ) :
    ‖Gi F y τ k - 1‖ ≤ Real.exp (∑ m ∈ Finset.range k, cc F y τ m) - 1 ∧
      ‖Gi F y τ k‖ ≤ Real.exp (∑ m ∈ Finset.range k, cc F y τ m) := by
  induction k with
  | zero => simp [Gi, norm_one_le]
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set B := NormedSpace.exp (-(yy F y m • Evec F τ m)) with hB
    have hx : ‖-(yy F y m • Evec F τ m)‖ ≤ cc F y τ m := by
      rw [norm_neg]; exact norm_factor_le F y τ m
    have hB1 : ‖B - 1‖ ≤ Real.exp (cc F y τ m) - 1 :=
      (norm_exp_sub_one_le _).trans (by gcongr)
    have hB2 : ‖B‖ ≤ Real.exp (cc F y τ m) :=
      (norm_exp_le norm_one_le _).trans (Real.exp_le_exp.2 hx)
    have e : Gi F y τ (m + 1) - 1 = (Gi F y τ m - 1) * B + (B - 1) := by
      simp only [Gi, hB, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [Finset.sum_range_succ, Real.exp_add]
    set S := ∑ x ∈ Finset.range m, cc F y τ x
    have hS : 1 ≤ Real.exp S := Real.one_le_exp (Finset.sum_nonneg fun i _ => cc_nonneg F y τ i)
    have hc : 1 ≤ Real.exp (cc F y τ m) := Real.one_le_exp (cc_nonneg F y τ m)
    constructor
    · rw [e]
      calc ‖(Gi F y τ m - 1) * B + (B - 1)‖ ≤ ‖Gi F y τ m - 1‖ * ‖B‖ + ‖B - 1‖ :=
            (norm_add_le _ _).trans (add_le_add_left (norm_mul_le _ _) _)
        _ ≤ (Real.exp S - 1) * Real.exp (cc F y τ m) + (Real.exp (cc F y τ m) - 1) := by
            gcongr
        _ = Real.exp S * Real.exp (cc F y τ m) - 1 := by ring
    · calc ‖Gi F y τ (m + 1)‖ = ‖Gi F y τ m * B‖ := rfl
        _ ≤ ‖Gi F y τ m‖ * ‖B‖ := norm_mul_le _ _
        _ ≤ Real.exp S * Real.exp (cc F y τ m) := by gcongr
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
