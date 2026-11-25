-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.exponent_fixed_instance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:59:28.732749+00:00
-- url     : https://prove2.me/submissions/1bda1525-d32c-4e41-9376-73018f486741

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstExp
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_exp_real_entry
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
open Matrix
namespace PI.ScMuExists.UnitaryGroupMassFormula
private theorem exists_unitary_diagonal_of_isHermitian {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), star U * U = 1 ∧ U * star U = 1 ∧
      X = U * diagonal (fun i => (d i : ℂ)) * star U := by
  have h1 : star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    first
      | exact hX.eigenvectorUnitary.2.1
      | exact (Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2)
      | exact Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
      | exact unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  have h2 : (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    first
      | exact hX.eigenvectorUnitary.2.2
      | exact (Matrix.mem_unitaryGroup_iff.mp hX.eigenvectorUnitary.2)
      | exact Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
      | exact unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
  refine ⟨hX.eigenvectorUnitary, hX.eigenvalues, h1, h2, ?_⟩
  first
    | (conv_lhs => rw [hX.spectral_theorem]); simp [Function.comp_def]
    | (conv_lhs => rw [hX.spectral_theorem]); simp [Function.comp_def, Unitary.conjStarAlgAut_apply]
    | (have h3 := hX.star_mul_self_mul_eq_diagonal
       calc X = (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
              (star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * X *
                (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) *
              star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
             simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
             rw [Matrix.mul_assoc, h2, Matrix.mul_one]
         _ = _ := by rw [h3]; simp [Function.comp_def])
end PI.ScMuExists.UnitaryGroupMassFormula
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution : InstExpFix := by
  intro n X hX w
  obtain ⟨U, d, hUU, hUU', hX'⟩ := exists_unitary_diagonal_of_isHermitian X hX
  have hexp : NormedSpace.exp X = U * diagonal (fun i => NormedSpace.exp (d i : ℂ)) * star U := by
    have hunit : IsUnit U := ⟨⟨U, star U, hUU', hUU⟩, rfl⟩
    have hinv : U⁻¹ = star U := Matrix.inv_eq_left_inv hUU
    rw [hX', ← hinv]
    have hd : NormedSpace.exp (diagonal (fun i => (d i : ℂ))) =
        diagonal (fun i => NormedSpace.exp (d i : ℂ)) := by
      rw [Matrix.exp_diagonal]
      congr 1
      funext i
      first
        | exact Pi.exp_apply _ _
        | simp [Pi.exp_def]
        | rfl
    first
      | rw [Matrix.exp_conj _ _ hunit, hd]
      | rw [Matrix.exp_conj ℂ _ _ hunit, hd]
  have inj : ∀ a b : Fin n → ℂ, U *ᵥ a = U *ᵥ b → a = b := by
    intro a b h
    have h2 := congrArg (fun v => star U *ᵥ v) h
    simpa only [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec] using h2
  obtain ⟨y, hy⟩ : ∃ y, y = star U *ᵥ w := ⟨_, rfl⟩
  have hw : w = U *ᵥ y := by rw [hy, Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
  have hXw : X *ᵥ w = U *ᵥ (fun i => (d i : ℂ) * y i) := by
    rw [hX', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy]
    congr 1
    funext i
    rw [Matrix.mulVec_diagonal]
  have hEw : NormedSpace.exp X *ᵥ w = U *ᵥ (fun i => NormedSpace.exp (d i : ℂ) * y i) := by
    rw [hexp, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy]
    congr 1
    funext i
    rw [Matrix.mulVec_diagonal]
  constructor
  · intro h
    have h1 : (fun i => NormedSpace.exp (d i : ℂ) * y i) = y := by
      apply inj
      rw [← hEw, h]
      exact hw
    rw [hXw]
    have h0 : (fun i => (d i : ℂ) * y i) = 0 := by
      funext i
      exact (inst_exp_real_entry (d i) (y i)).mp (congrFun h1 i)
    rw [h0, Matrix.mulVec_zero]
  · intro h
    rw [hXw] at h
    have h2 : (fun i => (d i : ℂ) * y i) = 0 := inj _ 0 (by rw [h, Matrix.mulVec_zero])
    rw [hEw]
    have h3 : (fun i => NormedSpace.exp (d i : ℂ) * y i) = y := by
      funext i
      exact (inst_exp_real_entry (d i) (y i)).mpr (congrFun h2 i)
    rw [h3, ← hw]
end PI.ScMuExists.UnitaryGroupMassFormula
