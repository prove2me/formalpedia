-- Prove2me | solution 1 for PositivityTheory.RL.Up.real_form_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:52.318484+00:00
-- url     : https://prove2.me/submissions/4819bc62-a396-4e44-9748-7a7c96c5a74f

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GroupGeneratedByExp
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieC
import Theorems.Thm_PositivityTheory_RL_Up_eq_trace
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Up
namespace PositivityTheory.RL.Up
theorem _root_.solution {β : Type} [Fintype β] [DecidableEq β] (τ : Matrix β β ℂ →ₗ[ℝ] Matrix β β ℂ)
    (hI : ∀ A, τ (I • A) = -(I • τ A)) (hτ : ∀ A, τ (τ A) = A) (ζ : Matrix β β ℂ →ₗ[ℝ] ℂ)
    (hb : ∀ X Y, τ X = X → τ Y = Y → τ (X * Y - Y * X) = X * Y - Y * X ∧ ζ (X * Y - Y * X) = 0) :
    ∃ c : ℂ, ∀ Z, τ Z = Z → ζ Z = c * Z.trace := by
  let P : Matrix β β ℂ → Matrix β β ℂ := fun A => (1 / 2 : ℝ) • (A + τ A)
  have hP : ∀ A, τ (P A) = P A := fun A => by simp only [P, map_smul, map_add, hτ, add_comm]
  let ξ0 : Matrix β β ℂ → ℂ := fun A => ζ (P A) - I * ζ (P (I • A))
  have add : ∀ A B, ξ0 (A + B) = ξ0 A + ξ0 B := fun A B => by
    simp only [ξ0, P, smul_add, map_add, map_smul]
    ring
  have rs : ∀ (r : ℝ) A, ξ0 (r • A) = r * ξ0 A := fun r A => by
    simp only [ξ0, P, smul_comm I r, smul_add, map_add, map_smul, real_smul]
    ring
  have is : ∀ A, ξ0 (I • A) = I * ξ0 A := fun A => by
    simp only [ξ0, P, smul_smul, I_mul_I, neg_smul, one_smul, smul_add, map_add, map_smul, map_neg, real_smul, smul_neg]
    linear_combination ((((1 / 2 : ℝ) : ℂ) * ζ (I • A) + ((1 / 2 : ℝ) : ℂ) * ζ (τ (I • A)))) * I_mul_I
  let ξ : Matrix β β ℂ →ₗ[ℂ] ℂ :=
    { toFun := ξ0
      map_add' := add
      map_smul' := fun c A => by
        have e : c • A = c.re • A + I • (c.im • A) := by
          ext i j
          simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, real_smul]
          linear_combination (-A i j) * re_add_im c
        rw [e, add, is, rs, rs, RingHom.id_apply, smul_eq_mul]
        linear_combination (ξ0 A) * re_add_im c }
  have fix : ∀ Z, τ Z = Z → ξ Z = ζ Z := fun Z hZ => by
    have e1 : P Z = Z := by
      simp only [P, hZ]
      module
    have e2 : P (I • Z) = 0 := by simp only [P, hI, hZ, add_neg_cancel, smul_zero]
    show ζ (P Z) - I * ζ (P (I • Z)) = _
    rw [e1, e2, map_zero, mul_zero, sub_zero]
  have dec : ∀ A, A = P A - I • P (I • A) := fun A => by
    simp only [P, hI]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul, real_smul]
    push_cast
    linear_combination ((A i j - τ A i j) / 2) * I_mul_I
  have br : ∀ X Y, τ X = X → τ Y = Y → ξ (X * Y - Y * X) = 0 := fun X Y hX hY => by
    rw [fix _ (hb X Y hX hY).1, (hb X Y hX hY).2]
  obtain ⟨c, hc⟩ := eq_trace ξ fun A B => by
    have h1 : ∀ X, τ X = X → ξ (X * B - B * X) = 0 := fun X hX => by
      have e : X * B - B * X = (X * P B - P B * X) - I • (X * P (I • B) - P (I • B) * X) := by
        conv_lhs => rw [dec B]
        simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        abel
      rw [e, map_sub, map_smul, br _ _ hX (hP _), br _ _ hX (hP _), smul_zero, sub_zero]
    have e : A * B - B * A = (P A * B - B * P A) - I • (P (I • A) * B - B * P (I • A)) := by
      conv_lhs => rw [dec A]
      simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      abel
    rw [e, map_sub, map_smul, h1 _ (hP _), h1 _ (hP _), smul_zero, sub_zero]
  exact ⟨c, fun Z hZ => by rw [← fix Z hZ, hc]⟩
end PositivityTheory.RL.Up
