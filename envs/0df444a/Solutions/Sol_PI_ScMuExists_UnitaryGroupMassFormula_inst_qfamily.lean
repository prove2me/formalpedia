-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.inst_qfamily
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:46:35.034084+00:00
-- url     : https://prove2.me/submissions/7d6005ad-9481-4307-8eac-44afdb2cc8ad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstAdapt
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_sign_real
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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin n) ℂ) (hQQ : Q * Q = Q)
    (hQJ : Qᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Q) :
    ∃ (W : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ),
      Wᴴ * Formalism.REAL.Jm ε * W =
        diagonal (fun i => if lam i = 0 then (0 : ℂ) else if 0 < lam i then 1 else -1) ∧
      Q * W = W ∧
      (∀ x : Fin n → ℂ, Q *ᵥ x = x → ∃ y : Fin n → ℂ, (∀ i, lam i = 0 → y i = 0) ∧ x = W *ᵥ y) ∧
      Fintype.card {i // lam i ≠ 0} = Q.rank ∧
      ∃ (U : Matrix (Fin n) (Fin n) ℂ) (s : Fin n → ℂ), W = Q * U * diagonal s := by
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJs : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a <;> simp [h]
  set J := Formalism.REAL.Jm ε with hJdef
  have hQJQ : Qᴴ * J * Q = J * Q := by rw [hQJ, Matrix.mul_assoc, hQQ]
  have hMh : (Qᴴ * J * Q).IsHermitian := by
    show (Qᴴ * J * Q)ᴴ = Qᴴ * J * Q
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJs,
      Matrix.mul_assoc]
  obtain ⟨V, μ, hVV, hVV', hM⟩ := exists_unitary_diagonal_of_isHermitian (Qᴴ * J * Q) hMh
  rw [hQJQ] at hM
  set s : Fin n → ℂ := fun i => if μ i = 0 then 0 else (((Real.sqrt |μ i|)⁻¹ : ℝ) : ℂ) with hsdef
  refine ⟨Q * V * diagonal s, μ, ?_, ?_, ?_, ?_, V, s, rfl⟩
  · have hD : star V * (J * Q) * V = diagonal (fun i => (μ i : ℂ)) := by
      rw [hM]
      calc star V * (V * diagonal (fun i => (μ i : ℂ)) * star V) * V
          = (star V * V) * diagonal (fun i => (μ i : ℂ)) * (star V * V) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hVV, Matrix.one_mul, Matrix.mul_one]
    have h1 : (Q * V * diagonal s)ᴴ * J * (Q * V * diagonal s) =
        (diagonal s)ᴴ * (star V * (Qᴴ * J * Q) * V) * diagonal s := by
      simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    rw [h1, hQJQ, hD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hμ : μ i = 0
    · simp [hsdef, hμ]
    · have hsr := inst_sign_real (μ i) hμ
      have hc : star (s i) * (μ i : ℂ) * s i =
          (((Real.sqrt |μ i|)⁻¹ * μ i * (Real.sqrt |μ i|)⁻¹ : ℝ) : ℂ) := by
        simp only [hsdef, hμ, if_false, Complex.star_def, Complex.conj_ofReal]
        first
          | (push_cast; ring)
          | push_cast
      simp only [Pi.star_apply]
      rw [hc, hsr, if_neg hμ]
      split_ifs <;> simp
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ]
  · intro x hx
    obtain ⟨z, hz⟩ : ∃ z : Fin n → ℂ, z = star V *ᵥ x := ⟨_, rfl⟩
    obtain ⟨w2, hw2⟩ : ∃ w2 : Fin n → ℂ, w2 = fun i => if μ i = 0 then z i else 0 := ⟨_, rfl⟩
    refine ⟨fun i => if μ i = 0 then 0 else (Real.sqrt |μ i| : ℂ) * z i, fun i hi => by simp [hi], ?_⟩
    have hVz : V *ᵥ z = x := by rw [hz, Matrix.mulVec_mulVec, hVV', Matrix.one_mulVec]
    have h1 : (J * Q) *ᵥ (V *ᵥ w2) = 0 := by
      rw [hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec w2 (star V) V, hVV,
        Matrix.one_mulVec]
      have h2 : diagonal (fun i => (μ i : ℂ)) *ᵥ w2 = 0 := by
        funext i
        rw [Matrix.mulVec_diagonal, hw2]
        by_cases hμ : μ i = 0 <;> simp [hμ]
      rw [h2, Matrix.mulVec_zero]
    have hkill : Q *ᵥ (V *ᵥ w2) = 0 := by
      calc Q *ᵥ (V *ᵥ w2) = (J * J * Q) *ᵥ (V *ᵥ w2) := by rw [hJJ, Matrix.one_mul]
        _ = J *ᵥ ((J * Q) *ᵥ (V *ᵥ w2)) := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = 0 := by rw [h1, Matrix.mulVec_zero]
    have hSy : diagonal s *ᵥ (fun i => if μ i = 0 then 0 else (Real.sqrt |μ i| : ℂ) * z i) =
        fun i => if μ i = 0 then 0 else z i := by
      funext i
      rw [Matrix.mulVec_diagonal]
      by_cases hμ : μ i = 0
      · simp [hμ]
      · have hpos : 0 < Real.sqrt |μ i| := Real.sqrt_pos.mpr (abs_pos.mpr hμ)
        simp only [hsdef, hμ, if_false]
        rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one, one_mul]
    have hsplit : z = (fun i => if μ i = 0 then 0 else z i) + w2 := by
      funext i
      rw [hw2]
      simp only [Pi.add_apply]
      split_ifs <;> simp
    calc x = Q *ᵥ x := hx.symm
      _ = Q *ᵥ (V *ᵥ z) := by rw [hVz]
      _ = Q *ᵥ (V *ᵥ (fun i => if μ i = 0 then 0 else z i)) + Q *ᵥ (V *ᵥ w2) := by
          conv_lhs => rw [hsplit]
          rw [Matrix.mulVec_add, Matrix.mulVec_add]
      _ = Q *ᵥ (V *ᵥ (fun i => if μ i = 0 then 0 else z i)) := by rw [hkill, add_zero]
      _ = (Q * V * diagonal s) *ᵥ
            (fun i => if μ i = 0 then 0 else (Real.sqrt |μ i| : ℂ) * z i) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hSy]
  · have hrk1 : (J * Q).rank = Q.rank :=
      Matrix.rank_mul_eq_right_of_isUnit_det J Q (Matrix.isUnit_det_of_left_inverse hJJ)
    have hVunit : IsUnit V.det := Matrix.isUnit_det_of_left_inverse hVV
    have hsVunit : IsUnit (star V).det := Matrix.isUnit_det_of_left_inverse hVV'
    rw [← hrk1, hM, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hsVunit,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVunit, Matrix.rank_diagonal]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun i => Complex.ofReal_ne_zero.symm)
end PI.ScMuExists.UnitaryGroupMassFormula
