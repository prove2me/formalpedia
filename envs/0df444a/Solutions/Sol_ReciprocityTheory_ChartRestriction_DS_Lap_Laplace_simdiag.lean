-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.simdiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:47.048797+00:00
-- url     : https://prove2.me/submissions/67ae4921-bff1-412a-be07-970b1a2f3ffa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_Laplace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
open scoped MatrixOrder
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
theorem _root_.solution {d : ℕ} (A C : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hC : C.IsHermitian) :
    ∃ P : Matrix (Fin d) (Fin d) ℝ, IsUnit P ∧ ∃ c : Fin d → ℝ,
      Pᵀ * A * P = 1 ∧ Pᵀ * C * P = diagonal c := by
  have spec : ∀ (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian),
      ∃ U : Matrix (Fin d) (Fin d) ℝ, Uᵀ * U = 1 ∧ Uᵀ * M * U = diagonal hM.eigenvalues := by
    intro M hM
    have hst : star (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) =
        (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᵀ := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    have h1 := Matrix.mem_unitaryGroup_iff'.1 hM.eigenvectorUnitary.2
    have h2 := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp] at h2
    rw [hst] at h1 h2
    obtain ⟨U, hU1, hU2⟩ : ∃ U : Matrix (Fin d) (Fin d) ℝ,
        Uᵀ * U = 1 ∧ M = U * diagonal hM.eigenvalues * Uᵀ := ⟨_, h1, h2⟩
    refine ⟨U, hU1, ?_⟩
    calc Uᵀ * M * U = Uᵀ * (U * diagonal hM.eigenvalues * Uᵀ) * U :=
          congrArg (fun X => Uᵀ * X * U) hU2
      _ = (Uᵀ * U) * diagonal hM.eigenvalues * (Uᵀ * U) := by simp only [Matrix.mul_assoc]
      _ = diagonal hM.eigenvalues := by rw [hU1, Matrix.one_mul, Matrix.mul_one]
  have hCt : Cᵀ = C := by
    have h := hC
    unfold Matrix.IsHermitian at h
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  obtain ⟨U, hU1, hU2⟩ := spec A hA.1
  obtain ⟨s, hs⟩ : ∃ s : Fin d → ℝ, ∀ i, s i * hA.1.eigenvalues i * s i = 1 := by
    refine ⟨fun i => (Real.sqrt (hA.1.eigenvalues i))⁻¹, fun i => ?_⟩
    have h0 := hA.eigenvalues_pos i
    rw [show (Real.sqrt (hA.1.eigenvalues i))⁻¹ * hA.1.eigenvalues i *
        (Real.sqrt (hA.1.eigenvalues i))⁻¹ =
        hA.1.eigenvalues i / (Real.sqrt (hA.1.eigenvalues i) * Real.sqrt (hA.1.eigenvalues i)) by ring,
      Real.mul_self_sqrt h0.le, div_self h0.ne']
  have hQ' : (U * diagonal s)ᵀ * A * (U * diagonal s) = 1 := by
    have e1 : (U * diagonal s)ᵀ * A * (U * diagonal s) = diagonal s * (Uᵀ * A * U) * diagonal s := by
      simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [e1, hU2, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hs i
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin d) (Fin d) ℝ, Qᵀ * A * Q = 1 := ⟨_, hQ'⟩
  have hC' : (Qᵀ * C * Q).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hCt, Matrix.mul_assoc]
  obtain ⟨V, hV1, hV2⟩ := spec _ hC'
  have hPA : (Q * V)ᵀ * A * (Q * V) = 1 := by
    have e : (Q * V)ᵀ * A * (Q * V) = Vᵀ * (Qᵀ * A * Q) * V := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e, hQ, Matrix.mul_one, hV1]
  have hPC : (Q * V)ᵀ * C * (Q * V) = diagonal hC'.eigenvalues := by
    have e : (Q * V)ᵀ * C * (Q * V) = Vᵀ * (Qᵀ * C * Q) * V := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e, hV2]
  have hdet := congrArg Matrix.det hPA
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  have hP : IsUnit (Q * V) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_mul]
    intro h0
    rw [h0] at hdet
    simp at hdet
  exact ⟨Q * V, hP, hC'.eigenvalues, hPA, hPC⟩
end ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
