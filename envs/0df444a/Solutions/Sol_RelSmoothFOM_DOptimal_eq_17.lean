-- Prove2me | solution 1 for RelSmoothFOM.DOptimal.eq_17
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:37:29.519631+00:00
-- url     : https://prove2.me/submissions/cee811ce-6559-4139-ad38-a9b591c8d174

import Mathlib
import Definitions.Def_RelSmoothFOM_DOptimal_Setting

set_option autoImplicit false
open Matrix
open RelSmoothFOM.DOptimal

/-- derivative of the log barrier at a positive point -/
theorem rsd_logBarrier_fderiv {n : ℕ} (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) (v : Fin n → ℝ) :
    fderiv ℝ (logBarrier : (Fin n → ℝ) → ℝ) x v = -∑ j, v j / x j := by
  have h : HasFDerivAt (logBarrier : (Fin n → ℝ) → ℝ)
      (-∑ j : Fin n, (x j)⁻¹ • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
    have h1 : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        HasFDerivAt (fun y : Fin n → ℝ => Real.log (y j))
          ((x j)⁻¹ • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
      intro j _
      exact (hasFDerivAt_apply j x).log (hx j).ne'
    have := (HasFDerivAt.sum h1).neg
    have hf : (logBarrier : (Fin n → ℝ) → ℝ) = -∑ i : Fin n, fun y : Fin n → ℝ => Real.log (y i) := by
      funext y
      simp [logBarrier]
    rw [hf]
    exact this
  rw [h.fderiv]
  simp [div_eq_inv_mul]

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

theorem rsd_c_le_xinv {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
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

theorem rsd_hessian_logBarrier {n : ℕ} (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) (v w : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ (logBarrier : (Fin n → ℝ) → ℝ)) x v w = ∑ j, v j * w j / x j ^ 2 := by
  have hopen : IsOpen {y : Fin n → ℝ | ∀ j, 0 < y j} := by
    have : {y : Fin n → ℝ | ∀ j, 0 < y j} = Set.pi Set.univ (fun _ => Set.Ioi 0) := by
      ext y; simp
    rw [this]
    exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioi)
  set L : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ) :=
    fun y => -∑ j : Fin n, (y j)⁻¹ • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) with hL
  have hev : fderiv ℝ (logBarrier : (Fin n → ℝ) → ℝ) =ᶠ[nhds x] L := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    ext1 v
    rw [rsd_logBarrier_fderiv y hy v]
    simp [hL, div_eq_inv_mul]
  rw [hev.fderiv_eq]
  have h1 : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      HasFDerivAt (fun y : Fin n → ℝ => (y j)⁻¹ • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))
        (((ContinuousLinearMap.toSpanSingleton ℝ (-(x j ^ 2)⁻¹)).comp
            (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)).smulRight
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
    intro j _
    have hd := hasFDerivAt_inv (𝕜 := ℝ) (hx j).ne'
    have hap : HasFDerivAt (fun y : Fin n → ℝ => y j)
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) x := hasFDerivAt_apply j x
    have := HasFDerivAt.comp x (g := fun t : ℝ => t⁻¹) hd hap
    exact HasFDerivAt.smul_const (c := fun y : Fin n → ℝ => (y j)⁻¹) this
      (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)
  have h2 := (HasFDerivAt.sum h1).neg
  have h3 : HasFDerivAt L (-∑ j : Fin n, ((ContinuousLinearMap.toSpanSingleton ℝ (-(x j ^ 2)⁻¹)).comp
            (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)).smulRight
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
    have hf : L = -∑ j : Fin n, fun y : Fin n → ℝ => (y j)⁻¹ • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) := by
      funext y; simp [hL]
    rw [hf]
    exact h2
  rw [h3.fderiv]
  simp [Finset.sum_apply, div_eq_mul_inv]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem solution {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (hH : H.rank = m) (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    let C := H.transpose * (H * Matrix.diagonal x * H.transpose)⁻¹ * H
    let Xinv := Matrix.diagonal (fun j => 1 / x j)
    (C.hadamard Xinv - C.hadamard C).PosSemidef ∧
    (Xinv.hadamard Xinv - C.hadamard Xinv).PosSemidef ∧
    Xinv.hadamard Xinv = Matrix.diagonal (fun j => 1 / x j ^ 2) ∧
    (∀ v w : Fin n → ℝ,
      fderiv ℝ (fderiv ℝ logBarrier) x v w =
        ∑ j, v j * w j / x j ^ 2) := by
  intro C Xinv
  classical
  have hX : (Matrix.diagonal x).PosDef := Matrix.PosDef.diagonal hx
  have hM : (H * Matrix.diagonal x * H.transpose).PosDef := by
    have := hX.mul_mul_conjTranspose_same (B := H) (rsd_vecMul_injective H hH)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hCpsd : C.PosSemidef := by
    have := hM.inv.posSemidef.conjTranspose_mul_mul_same H
    simpa [C, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hXinv : Xinv.PosSemidef :=
    (Matrix.PosDef.diagonal (fun j => one_div_pos.mpr (hx j))).posSemidef
  have hdiff : (Xinv - C).PosSemidef := rsd_c_le_xinv H hH x hx
  refine ⟨?_, ?_, ?_, rsd_hessian_logBarrier x hx⟩
  · have := hCpsd.hadamard hdiff
    have e : C.hadamard Xinv - C.hadamard C = C.hadamard (Xinv - C) := by
      ext i j; simp [Matrix.hadamard, mul_sub]
    rw [e]; exact this
  · have := hdiff.hadamard hXinv
    have e : Xinv.hadamard Xinv - C.hadamard Xinv = (Xinv - C).hadamard Xinv := by
      ext i j; simp [Matrix.hadamard, sub_mul]
    rw [e]; exact this
  · ext i j
    by_cases h : i = j
    · subst h; simp [Xinv, Matrix.hadamard]; ring
    · simp [Xinv, Matrix.hadamard, h]
