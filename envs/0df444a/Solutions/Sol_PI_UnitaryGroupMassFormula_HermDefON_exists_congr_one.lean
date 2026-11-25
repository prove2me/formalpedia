-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.HermDefON.exists_congr_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:11.3427+00:00
-- url     : https://prove2.me/submissions/86f349e3-1ee2-4868-8308-98662265a8f6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_HermDefONFamily
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDefiniteOrthonormal_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace PI.UnitaryGroupMassFormula.HermDefON
open Matrix
open scoped ComplexOrder
private theorem exists_unitary_diagonal_pos_of_posDef {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℝ), Uᴴ * U = 1 ∧ (∀ i, 0 < μ i) ∧
      G = U * diagonal (fun i => (μ i : ℂ)) * Uᴴ := by
  refine ⟨(hG.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), hG.1.eigenvalues, ?_,
    fun i => hG.eigenvalues_pos i, ?_⟩
  · have h := hG.1.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff'] at h
    simpa [Matrix.star_eq_conjTranspose] using h
  · have h := hG.1.spectral_theorem
    refine h.trans ?_
    rfl
end PI.UnitaryGroupMassFormula.HermDefON
end

set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.HermDefON
open Matrix
open scoped ComplexOrder
namespace PI.UnitaryGroupMassFormula.HermDefON
theorem _root_.solution {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) :
    ∃ y : Matrix (Fin n) (Fin n) ℂ, IsUnit y.det ∧ yᴴ * G * y = 1 := by
  classical
  obtain ⟨U, μ, hUU, hμ, hG'⟩ := exists_unitary_diagonal_pos_of_posDef G hG
  have hr : ∀ i, Real.sqrt (μ i) * (Real.sqrt (μ i))⁻¹ = 1 := fun i =>
    mul_inv_cancel₀ (Real.sqrt_pos.mpr (hμ i)).ne'
  have hr2 : ∀ i, (Real.sqrt (μ i))⁻¹ * μ i * (Real.sqrt (μ i))⁻¹ = 1 := by
    intro i
    have hs : Real.sqrt (μ i) ≠ 0 := (Real.sqrt_pos.mpr (hμ i)).ne'
    have hsq : Real.sqrt (μ i) * Real.sqrt (μ i) = μ i := Real.mul_self_sqrt (hμ i).le
    calc (Real.sqrt (μ i))⁻¹ * μ i * (Real.sqrt (μ i))⁻¹
        = (Real.sqrt (μ i))⁻¹ * (Real.sqrt (μ i) * Real.sqrt (μ i)) * (Real.sqrt (μ i))⁻¹ := by
          rw [hsq]
      _ = 1 := by rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul, mul_inv_cancel₀ hs]
  let d : Fin n → ℂ := fun i => (((Real.sqrt (μ i))⁻¹ : ℝ) : ℂ)
  let e : Fin n → ℂ := fun i => ((Real.sqrt (μ i) : ℝ) : ℂ)
  have hde : ∀ i, e i * d i = 1 := by
    intro i
    show ((Real.sqrt (μ i) : ℝ) : ℂ) * (((Real.sqrt (μ i))⁻¹ : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, hr i, Complex.ofReal_one]
  have hdd : ∀ i, d i * (μ i : ℂ) * d i = 1 := by
    intro i
    show (((Real.sqrt (μ i))⁻¹ : ℝ) : ℂ) * (μ i : ℂ) * (((Real.sqrt (μ i))⁻¹ : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hr2 i, Complex.ofReal_one]
  have hdH : (diagonal d)ᴴ = diagonal d := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [d]
  refine ⟨U * diagonal d, ?_, ?_⟩
  · have h : diagonal e * Uᴴ * (U * diagonal d) = 1 := by
      calc diagonal e * Uᴴ * (U * diagonal d) = diagonal e * (Uᴴ * U) * diagonal d := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
          rw [hUU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          simp only [hde]
          exact Matrix.diagonal_one
    exact Matrix.isUnit_det_of_left_inverse h
  · rw [Matrix.conjTranspose_mul, hdH, hG']
    calc diagonal d * Uᴴ * (U * diagonal (fun i => (μ i : ℂ)) * Uᴴ) * (U * diagonal d)
        = diagonal d * (Uᴴ * U) * diagonal (fun i => (μ i : ℂ)) * (Uᴴ * U) * diagonal d := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hUU, Matrix.mul_one, Matrix.mul_one, Matrix.diagonal_mul_diagonal,
          Matrix.diagonal_mul_diagonal]
        simp only [hdd]
        exact Matrix.diagonal_one
end PI.UnitaryGroupMassFormula.HermDefON
