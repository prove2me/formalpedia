-- Prove2me | solution 1 for WildeQIT.Purification.exists_unitary_eq_mul_of_mul_conjTranspose_eq
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T19:24:47.349204+00:00
-- url     : https://prove2.me/submissions/f5a9fdc8-118f-4c64-b888-7e4e24e706c1

import Mathlib
import Theorems.Thm_WildeQIT_Purification_exists_linearIsometry_apply_eq_of_norm_eq

open Matrix WildeQIT.Purification

theorem solution {a n : Type*} [Fintype a] [Fintype n] [DecidableEq n]
    (A B : Matrix a n ℂ) (h : A * Aᴴ = B * Bᴴ) :
    ∃ U ∈ Matrix.unitaryGroup n ℂ, A = B * U := by
  classical
  set f := Matrix.toEuclideanLin Aᴴ
  set g := Matrix.toEuclideanLin Bᴴ
  have hadjf : LinearMap.adjoint (Matrix.toEuclideanLin Aᴴ) = Matrix.toEuclideanLin A := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, conjTranspose_conjTranspose]
  have hadjg : LinearMap.adjoint (Matrix.toEuclideanLin Bᴴ) = Matrix.toEuclideanLin B := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, conjTranspose_conjTranspose]
  have key : ∀ v, Matrix.toEuclideanLin A (f v) = Matrix.toEuclideanLin B (g v) := by
    intro v
    ext i
    simp [f, g, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, h]
  have hnorm : ∀ v, ‖f v‖ = ‖g v‖ := by
    intro v
    have hi : (inner ℂ (f v) (f v)) = inner ℂ (g v) (g v) := by
      rw [← LinearMap.adjoint_inner_right, ← LinearMap.adjoint_inner_right, hadjf, hadjg, key]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hi
    have hi' : ‖f v‖ ^ 2 = ‖g v‖ ^ 2 := by exact_mod_cast hi
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hi'
  obtain ⟨T, hT⟩ := exists_linearIsometry_apply_eq_of_norm_eq f g hnorm
  set M : Matrix n n ℂ := Matrix.toEuclideanLin.symm T.toLinearMap
  have hM : Matrix.toEuclideanLin M = T.toLinearMap := by simp [M]
  have hcomp : ∀ (P : Matrix n n ℂ) (Q : Matrix n a ℂ) (v : EuclideanSpace ℂ a),
      Matrix.toEuclideanLin (P * Q) v = Matrix.toEuclideanLin P (Matrix.toEuclideanLin Q v) := by
    intro P Q v
    ext j
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
  have hMB : M * Bᴴ = Aᴴ := by
    apply Matrix.toEuclideanLin.injective
    ext v i
    rw [hcomp, hM]
    exact congrArg (fun w => w.ofLp i) (hT v)
  have hMM : Mᴴ * M = 1 := by
    apply Matrix.toEuclideanLin.injective
    have h1 := LinearIsometry.adjoint_comp_self' T
    rw [← hM, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h1
    ext v i
    have := congrArg (fun w => w i) (LinearMap.congr_fun h1 v)
    simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec] using this
  refine ⟨Mᴴ, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    simpa [star_eq_conjTranspose] using hMM
  · have := congrArg conjTranspose hMB
    simpa [conjTranspose_mul] using this.symm
