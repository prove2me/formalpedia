-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_norm_G_sub_one_le_8a8a31fefc56
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:13:00.0296+00:00
-- url     : https://prove2.me/submissions/980e4552-a538-492b-89aa-d4ee3dc22ed0

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
    ‖G F y τ k - 1‖ ≤ Real.exp (∑ m ∈ Finset.range k, cc F y τ m) - 1 ∧
      ‖G F y τ k‖ ≤ Real.exp (∑ m ∈ Finset.range k, cc F y τ m) := by
  induction k with
  | zero => simp [G, norm_one_le]
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set A := NormedSpace.exp (yy F y m • Evec F τ m) with hA
    have hx := norm_factor_le F y τ m
    have hA1 : ‖A - 1‖ ≤ Real.exp (cc F y τ m) - 1 :=
      (norm_exp_sub_one_le _).trans (by gcongr)
    have hA2 : ‖A‖ ≤ Real.exp (cc F y τ m) :=
      (norm_exp_le norm_one_le _).trans (Real.exp_le_exp.2 hx)
    have e : G F y τ (m + 1) - 1 = A * (G F y τ m - 1) + (A - 1) := by
      simp only [G, hA, Matrix.mul_sub, Matrix.mul_one]; abel
    rw [Finset.sum_range_succ, Real.exp_add]
    set S := ∑ x ∈ Finset.range m, cc F y τ x
    have hS : 1 ≤ Real.exp S := Real.one_le_exp (Finset.sum_nonneg fun i _ => cc_nonneg F y τ i)
    have hc : 1 ≤ Real.exp (cc F y τ m) := Real.one_le_exp (cc_nonneg F y τ m)
    constructor
    · rw [e]
      calc ‖A * (G F y τ m - 1) + (A - 1)‖ ≤ ‖A‖ * ‖G F y τ m - 1‖ + ‖A - 1‖ :=
            (norm_add_le _ _).trans (add_le_add_left (norm_mul_le _ _) _)
        _ ≤ Real.exp (cc F y τ m) * (Real.exp S - 1) + (Real.exp (cc F y τ m) - 1) := by
            gcongr
        _ = Real.exp S * Real.exp (cc F y τ m) - 1 := by ring
    · calc ‖G F y τ (m + 1)‖ = ‖A * G F y τ m‖ := rfl
        _ ≤ ‖A‖ * ‖G F y τ m‖ := norm_mul_le _ _
        _ ≤ Real.exp (cc F y τ m) * Real.exp S := by gcongr
        _ = Real.exp S * Real.exp (cc F y τ m) := by ring
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
