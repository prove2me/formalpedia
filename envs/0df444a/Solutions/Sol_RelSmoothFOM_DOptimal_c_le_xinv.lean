-- Prove2me | solution 1 for RelSmoothFOM.DOptimal.c_le_xinv
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:31:57.2128+00:00
-- url     : https://prove2.me/submissions/9b0e0d12-63a4-4c53-bb45-b973109cedc3

import Mathlib
import Definitions.Def_RelSmoothFOM_DOptimal_Setting

set_option autoImplicit false
open Matrix

theorem rsd_vecMul_injective {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) (hH : H.rank = m) :
    Function.Injective H.vecMul := by
  have h1 : Hᵀ.rank = m := by rw [Matrix.rank_transpose, hH]
  have h2 : Function.Injective Hᵀ.mulVec := by
    have := LinearMap.finrank_range_add_finrank_ker (Hᵀ.mulVecLin)
    have h3 : Module.finrank ℝ (LinearMap.range Hᵀ.mulVecLin) = m := h1
    have h4 : Module.finrank ℝ (Fin m → ℝ) = m := by simp
    have h5 : Module.finrank ℝ (LinearMap.ker Hᵀ.mulVecLin) = 0 := by omega
    have h6 : LinearMap.ker Hᵀ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h5
    exact LinearMap.ker_eq_bot.mp h6
  intro a b hab
  apply h2
  show Hᵀ *ᵥ a = Hᵀ *ᵥ b
  rw [Matrix.mulVec_transpose, Matrix.mulVec_transpose]
  exact hab

theorem solution {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (hH : H.rank = m) (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    (Matrix.diagonal (fun j => 1 / x j) -
      H.transpose * (H * Matrix.diagonal x * H.transpose)⁻¹ * H).PosSemidef := by
  classical
  have hX : (Matrix.diagonal x).PosDef := Matrix.PosDef.diagonal hx
  have hM : (H * Matrix.diagonal x * H.transpose).PosDef := by
    have := hX.mul_mul_conjTranspose_same (B := H) (rsd_vecMul_injective H hH)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  set M := H * Matrix.diagonal x * H.transpose with hMdef
  have hMu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  have hMi : M⁻¹.PosDef := hM.inv
  have hMMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMu
  have hDiag : (Matrix.diagonal (fun j => 1 / x j)).PosDef :=
    Matrix.PosDef.diagonal (fun j => one_div_pos.mpr (hx j))
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.sub hDiag.1 ?_
    have := Matrix.isHermitian_conjTranspose_mul_mul H hMi.1
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · intro v
    set w : Fin m → ℝ := M⁻¹ *ᵥ (H *ᵥ v) with hw
    set u : Fin n → ℝ := Hᵀ *ᵥ w with hu
    have e1 : M *ᵥ w = H *ᵥ v := by
      rw [hw, Matrix.mulVec_mulVec, hMMi, Matrix.one_mulVec]
    have e3 : v ⬝ᵥ u = (H *ᵥ v) ⬝ᵥ w := by
      rw [hu, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have e2 : ∑ j, x j * u j ^ 2 = w ⬝ᵥ (H *ᵥ v) := by
      rw [← e1, hMdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose]
      simp only [Matrix.mulVec_diagonal, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hu]; ring
    have hq : v ⬝ᵥ u = ∑ j, x j * u j ^ 2 := by
      rw [e2, e3, dotProduct_comm]
    have hT : v ⬝ᵥ (Matrix.diagonal (fun j => 1 / x j) *ᵥ v) = ∑ j, v j ^ 2 / x j := by
      simp only [Matrix.mulVec_diagonal, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    have hexp : ∑ j, x j * (u j - v j / x j) ^ 2 =
        (∑ j, x j * u j ^ 2) - 2 * (v ⬝ᵥ u) + ∑ j, v j ^ 2 / x j := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := (hx j).ne'
      field_simp
      ring
    have hnn : 0 ≤ ∑ j, x j * (u j - v j / x j) ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hx j).le (sq_nonneg _)
    have hfin : v ⬝ᵥ ((Matrix.diagonal (fun j => 1 / x j) -
        Hᵀ * M⁻¹ * H) *ᵥ v) = (∑ j, v j ^ 2 / x j) - v ⬝ᵥ u := by
      rw [Matrix.sub_mulVec, dotProduct_sub, hT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [star_trivial]
    rw [hfin]
    rw [hexp, ← hq] at hnn
    linarith
