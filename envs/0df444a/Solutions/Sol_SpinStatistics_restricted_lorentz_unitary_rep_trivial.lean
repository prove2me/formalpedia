-- Prove2me | solution 1 for SpinStatistics.restricted_lorentz_unitary_rep_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T18:45:00.006274+00:00
-- url     : https://prove2.me/submissions/e4b8ea5e-b33c-4b3f-b8a4-3064e13e7abf

import Mathlib
import Definitions.Def_ChatterjeeQFT_SL2C
import Definitions.Def_SpinStatistics_Defs

/-! 5e3e8fe0 SpinStatistics.restricted_lorentz_unitary_rep_trivial. SL(2,C) layer copied from the 00751584 proof (ChatterjeeQFT.kappa_surjective_two_to_one) (Chatterjee, Lectures on QFT, 25).
Kernel: if `κ(A) = κ(B)` then `C = B⁻¹A` satisfies `C M(x) Cᴴ = M(x)`; `x = e₀` gives `C` unitary,
so `C` commutes with `σ₁, σ₃`, hence `C = c·1` with `c² = det C = 1`.
Surjectivity: for `L ∈ SO(1,3)` put `N = Σ L_{μν} σ_μ σ_ν`.  Using the Lorentz relations
`LᵀηL = η`, `LηLᵀ = η` and the Jacobi relations between complementary `2×2` minors (from
`adj L = ηLᵀη`), one has `N M(x) Nᴴ = 4 tr(L) M(Lx)`.  If `tr L > 0`, `A = N/(2s)` with
`s² = det N / 4` works.  In general one of `tr(L D_k)` is positive (they sum to `4 L₀₀`), where
`D_k = κ(iσ_k)` are the rotations by `π`, and `L = κ(A')κ(iσ_k)`.
No `Theorems.*` module is imported. -/

set_option autoImplicit false
set_option linter.all false

open Matrix
open scoped ComplexOrder

namespace ChatterjeeQFTKappa

open ChatterjeeQFT

theorem hermOfVec_conjTranspose (x : Fin 4 → ℝ) : (hermOfVec x)ᴴ = hermOfVec x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermOfVec, Matrix.conjTranspose_apply, Complex.ext_iff]

theorem vecOfHerm_hermOfVec (x : Fin 4 → ℝ) : vecOfHerm (hermOfVec x) = x := by
  ext i
  fin_cases i <;> simp [vecOfHerm, hermOfVec, Complex.div_re, Complex.normSq] <;> ring_nf

theorem hermOfVec_vecOfHerm (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : Hᴴ = H) :
    hermOfVec (vecOfHerm H) = H := by
  have h00 : (H 0 0).im = 0 := by
    have := congrFun (congrFun hH 0) 0
    simp [Matrix.conjTranspose_apply, Complex.ext_iff] at this
    linarith
  have h11 : (H 1 1).im = 0 := by
    have := congrFun (congrFun hH 1) 1
    simp [Matrix.conjTranspose_apply, Complex.ext_iff] at this
    linarith
  have h10 := congrFun (congrFun hH 1) 0
  simp [Matrix.conjTranspose_apply, Complex.ext_iff] at h10
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermOfVec, vecOfHerm, Complex.ext_iff, Complex.div_re, Complex.div_im,
      Complex.normSq] <;> constructor <;> linarith

theorem det_hermOfVec (x : Fin 4 → ℝ) :
    (hermOfVec x).det = ((minkowskiSq x : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp only [hermOfVec, minkowskiSq, minkowskiInner, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.head_fin_const]
  push_cast
  linear_combination (x 2 : ℂ) ^ 2 * Complex.I_sq

theorem hermOfVec_kappa (B : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    hermOfVec (kappa B x) = B * hermOfVec x * Bᴴ := by
  unfold kappa
  apply hermOfVec_vecOfHerm
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hermOfVec_conjTranspose, Matrix.mul_assoc]

theorem kappa_kappa (B C : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    kappa B (kappa C x) = kappa (B * C) x := by
  rw [kappa, hermOfVec_kappa, kappa, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem kappa_of_herm (A : Matrix (Fin 2) (Fin 2) ℂ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ x, A * hermOfVec x * Aᴴ = hermOfVec (L *ᵥ x)) (x : Fin 4 → ℝ) :
    kappa A x = L *ᵥ x := by
  unfold kappa
  rw [h x, vecOfHerm_hermOfVec]

theorem hermOfVec_e0 : hermOfVec ![1, 0, 0, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOfVec]

/-! ## The kernel -/

theorem kappa_neg (B : Matrix (Fin 2) (Fin 2) ℂ) : kappa (-B) = kappa B := by
  funext x
  simp [kappa, Matrix.conjTranspose_neg]

theorem kernel_mp (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) (hB : B.det = 1)
    (h : kappa A = kappa B) : A = B ∨ A = -B := by
  have hBu : IsUnit B.det := by rw [hB]; exact isUnit_one
  have hBHu : IsUnit Bᴴ.det := by rw [Matrix.det_conjTranspose, hB, star_one]; exact isUnit_one
  set C := B⁻¹ * A with hCdef
  have hBC : B * C = A := by
    rw [hCdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul]
  have hC : ∀ x, C * hermOfVec x * Cᴴ = hermOfVec x := by
    intro x
    have h1 : A * hermOfVec x * Aᴴ = B * hermOfVec x * Bᴴ := by
      rw [← hermOfVec_kappa, ← hermOfVec_kappa, h]
    rw [← hBC, Matrix.conjTranspose_mul] at h1
    have h2 : B * (C * hermOfVec x * Cᴴ) * Bᴴ = B * hermOfVec x * Bᴴ := by
      rw [← h1]; simp only [Matrix.mul_assoc]
    calc C * hermOfVec x * Cᴴ = B⁻¹ * (B * (C * hermOfVec x * Cᴴ) * Bᴴ) * Bᴴ⁻¹ := by
          rw [Matrix.mul_assoc B, Matrix.nonsing_inv_mul_cancel_left _ _ hBu,
            Matrix.mul_nonsing_inv_cancel_right _ _ hBHu]
      _ = B⁻¹ * (B * hermOfVec x * Bᴴ) * Bᴴ⁻¹ := by rw [h2]
      _ = hermOfVec x := by
          rw [Matrix.mul_assoc B, Matrix.nonsing_inv_mul_cancel_left _ _ hBu,
            Matrix.mul_nonsing_inv_cancel_right _ _ hBHu]
  have hCC : C * Cᴴ = 1 := by
    have := hC ![1, 0, 0, 0]
    rwa [hermOfVec_e0, Matrix.mul_one] at this
  have hCC' : Cᴴ * C = 1 := mul_eq_one_comm.mp hCC
  have hcomm : ∀ x, C * hermOfVec x = hermOfVec x * C := by
    intro x
    calc C * hermOfVec x = C * hermOfVec x * (Cᴴ * C) := by rw [hCC', Matrix.mul_one]
      _ = (C * hermOfVec x * Cᴴ) * C := by simp only [Matrix.mul_assoc]
      _ = hermOfVec x * C := by rw [hC x]
  have h3 := hcomm ![0, 0, 0, 1]
  have h1 := hcomm ![0, 1, 0, 0]
  have a01 := congrFun (congrFun h3 0) 1
  have a10 := congrFun (congrFun h3 1) 0
  have b01 := congrFun (congrFun h1 0) 1
  simp [hermOfVec, Matrix.mul_apply, Fin.sum_univ_two] at a01 a10 b01
  have hdC : C.det = 1 := by
    rw [hCdef, Matrix.det_mul, Matrix.det_nonsing_inv, hB, hA]
    simp
  rw [Matrix.det_fin_two] at hdC
  have c01 : C 0 1 = 0 := by linear_combination (-1 / 2 : ℂ) * a01
  have c10 : C 1 0 = 0 := by linear_combination (1 / 2 : ℂ) * a10
  have hsq : C 0 0 * C 0 0 = 1 := by
    rw [c01, c10, ← b01] at hdC
    linear_combination hdC
  rcases mul_self_eq_one_iff.mp hsq with h0 | h0
  · left
    have hC1 : C = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [c01, c10, ← b01, h0]
    rw [← hBC, hC1, Matrix.mul_one]
  · right
    have hC1 : C = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [c01, c10, ← b01, h0]
    rw [← hBC, hC1, Matrix.mul_neg, Matrix.mul_one]

theorem kernel (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) (hB : B.det = 1) :
    kappa A = kappa B ↔ (A = B ∨ A = -B) := by
  refine ⟨kernel_mp A B hA hB, ?_⟩
  rintro (rfl | rfl)
  · rfl
  · exact kappa_neg B

/-! ## The Minkowski metric -/

theorem minkowskiInner_polar (x y : Fin 4 → ℝ) :
    minkowskiInner x y = (minkowskiSq (x + y) - minkowskiSq (x - y)) / 4 := by
  simp only [minkowskiSq, minkowskiInner, Pi.add_apply, Pi.sub_apply]
  ring

theorem lorentz_inner (N : Matrix (Fin 4) (Fin 4) ℝ)
    (hN : ∀ x, minkowskiSq (N *ᵥ x) = minkowskiSq x) (x y : Fin 4 → ℝ) :
    minkowskiInner (N *ᵥ x) (N *ᵥ y) = minkowskiInner x y := by
  rw [minkowskiInner_polar, minkowskiInner_polar x y, ← Matrix.mulVec_add, ← Matrix.mulVec_sub,
    hN, hN]

/-- The Minkowski metric `diag(1,-1,-1,-1)`. -/
def eta : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, -1, -1, -1]

theorem lorentz_matrix (N : Matrix (Fin 4) (Fin 4) ℝ)
    (hN : ∀ x, minkowskiSq (N *ᵥ x) = minkowskiSq x) : Nᵀ * eta * N = eta := by
  ext i j
  have h := lorentz_inner N hN (Pi.single i 1) (Pi.single j 1)
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  fin_cases i <;> fin_cases j <;>
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four, minkowskiInner] at h ⊢ <;>
    linarith

theorem eta_mul_eta : eta * eta = 1 := by
  rw [eta, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

theorem adjugate_lorentz (N : Matrix (Fin 4) (Fin 4) ℝ) (h : Nᵀ * eta * N = eta) :
    adjugate N = N.det • (eta * Nᵀ * eta) := by
  have hleft : (eta * Nᵀ * eta) * N = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Nᵀ, h, eta_mul_eta]
  have hright : N * (eta * Nᵀ * eta) = 1 := mul_eq_one_comm.mp hleft
  calc adjugate N = adjugate N * (N * (eta * Nᵀ * eta)) := by rw [hright, Matrix.mul_one]
    _ = (adjugate N * N) * (eta * Nᵀ * eta) := (Matrix.mul_assoc _ _ _).symm
    _ = N.det • (eta * Nᵀ * eta) := by rw [adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

/-! ## The spinor `N = Σ L_{μν} σ_μ σ_ν` -/

/-- `N = Σ_{μ,ν} L_{μν} σ_μ σ_ν`, written out entrywise. -/
def Nmat (L : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨L 0 0 + L 1 1 + L 2 2 + L 3 3 + L 0 3 + L 3 0, L 1 2 - L 2 1⟩,
     ⟨L 0 1 + L 1 0 + L 3 1 - L 1 3, L 2 3 - L 3 2 - L 0 2 - L 2 0⟩;
     ⟨L 0 1 + L 1 0 - L 3 1 + L 1 3, L 2 3 - L 3 2 + L 0 2 + L 2 0⟩,
     ⟨L 0 0 + L 1 1 + L 2 2 + L 3 3 - L 0 3 - L 3 0, L 2 1 - L 1 2⟩]

set_option maxHeartbeats 4000000 in
theorem key (L : Matrix (Fin 4) (Fin 4) ℝ) (hG : Lᵀ * eta * L = eta) (hdet : L.det = 1)
    (x : Fin 4 → ℝ) :
    Nmat L * hermOfVec x * (Nmat L)ᴴ =
      ((4 * (L 0 0 + L 1 1 + L 2 2 + L 3 3) : ℝ) : ℂ) • hermOfVec (L *ᵥ x) := by
  have hleft : (eta * Lᵀ * eta) * L = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Lᵀ, hG, eta_mul_eta]
  have hright : L * (eta * Lᵀ * eta) = 1 := mul_eq_one_comm.mp hleft
  have hH : L * eta * Lᵀ = eta := by
    calc L * eta * Lᵀ = L * (eta * Lᵀ * eta) * eta := by
          simp only [Matrix.mul_assoc, eta_mul_eta, Matrix.mul_one]
      _ = eta := by rw [hright, Matrix.one_mul]
  have hadj : adjugate L = eta * Lᵀ * eta := by
    rw [adjugate_lorentz L hG, hdet, one_smul]
  have e00 : ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) = L 0 0 := by
    have h := congrFun (congrFun hadj 0) 0
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e01 : (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) = (-L 1 0) := by
    have h := congrFun (congrFun hadj 0) 1
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e02 : ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) = (-L 2 0) := by
    have h := congrFun (congrFun hadj 0) 2
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e03 : (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) = (-L 3 0) := by
    have h := congrFun (congrFun hadj 0) 3
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e10 : (-(L 1 0 * L 2 2 * L 3 3 - L 1 0 * L 2 3 * L 3 2 - L 1 2 * L 2 0 * L 3 3 + L 1 2 * L 2 3 * L 3 0 + L 1 3 * L 2 0 * L 3 2 - L 1 3 * L 2 2 * L 3 0)) = (-L 0 1) := by
    have h := congrFun (congrFun hadj 1) 0
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e11 : ((L 0 0 * L 2 2 * L 3 3 - L 0 0 * L 2 3 * L 3 2 - L 0 2 * L 2 0 * L 3 3 + L 0 2 * L 2 3 * L 3 0 + L 0 3 * L 2 0 * L 3 2 - L 0 3 * L 2 2 * L 3 0)) = L 1 1 := by
    have h := congrFun (congrFun hadj 1) 1
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e12 : (-(L 0 0 * L 1 2 * L 3 3 - L 0 0 * L 1 3 * L 3 2 - L 0 2 * L 1 0 * L 3 3 + L 0 2 * L 1 3 * L 3 0 + L 0 3 * L 1 0 * L 3 2 - L 0 3 * L 1 2 * L 3 0)) = L 2 1 := by
    have h := congrFun (congrFun hadj 1) 2
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e13 : ((L 0 0 * L 1 2 * L 2 3 - L 0 0 * L 1 3 * L 2 2 - L 0 2 * L 1 0 * L 2 3 + L 0 2 * L 1 3 * L 2 0 + L 0 3 * L 1 0 * L 2 2 - L 0 3 * L 1 2 * L 2 0)) = L 3 1 := by
    have h := congrFun (congrFun hadj 1) 3
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e20 : ((L 1 0 * L 2 1 * L 3 3 - L 1 0 * L 2 3 * L 3 1 - L 1 1 * L 2 0 * L 3 3 + L 1 1 * L 2 3 * L 3 0 + L 1 3 * L 2 0 * L 3 1 - L 1 3 * L 2 1 * L 3 0)) = (-L 0 2) := by
    have h := congrFun (congrFun hadj 2) 0
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e21 : (-(L 0 0 * L 2 1 * L 3 3 - L 0 0 * L 2 3 * L 3 1 - L 0 1 * L 2 0 * L 3 3 + L 0 1 * L 2 3 * L 3 0 + L 0 3 * L 2 0 * L 3 1 - L 0 3 * L 2 1 * L 3 0)) = L 1 2 := by
    have h := congrFun (congrFun hadj 2) 1
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e22 : ((L 0 0 * L 1 1 * L 3 3 - L 0 0 * L 1 3 * L 3 1 - L 0 1 * L 1 0 * L 3 3 + L 0 1 * L 1 3 * L 3 0 + L 0 3 * L 1 0 * L 3 1 - L 0 3 * L 1 1 * L 3 0)) = L 2 2 := by
    have h := congrFun (congrFun hadj 2) 2
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e23 : (-(L 0 0 * L 1 1 * L 2 3 - L 0 0 * L 1 3 * L 2 1 - L 0 1 * L 1 0 * L 2 3 + L 0 1 * L 1 3 * L 2 0 + L 0 3 * L 1 0 * L 2 1 - L 0 3 * L 1 1 * L 2 0)) = L 3 2 := by
    have h := congrFun (congrFun hadj 2) 3
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e30 : (-(L 1 0 * L 2 1 * L 3 2 - L 1 0 * L 2 2 * L 3 1 - L 1 1 * L 2 0 * L 3 2 + L 1 1 * L 2 2 * L 3 0 + L 1 2 * L 2 0 * L 3 1 - L 1 2 * L 2 1 * L 3 0)) = (-L 0 3) := by
    have h := congrFun (congrFun hadj 3) 0
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e31 : ((L 0 0 * L 2 1 * L 3 2 - L 0 0 * L 2 2 * L 3 1 - L 0 1 * L 2 0 * L 3 2 + L 0 1 * L 2 2 * L 3 0 + L 0 2 * L 2 0 * L 3 1 - L 0 2 * L 2 1 * L 3 0)) = L 1 3 := by
    have h := congrFun (congrFun hadj 3) 1
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e32 : (-(L 0 0 * L 1 1 * L 3 2 - L 0 0 * L 1 2 * L 3 1 - L 0 1 * L 1 0 * L 3 2 + L 0 1 * L 1 2 * L 3 0 + L 0 2 * L 1 0 * L 3 1 - L 0 2 * L 1 1 * L 3 0)) = L 2 3 := by
    have h := congrFun (congrFun hadj 3) 2
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e33 : ((L 0 0 * L 1 1 * L 2 2 - L 0 0 * L 1 2 * L 2 1 - L 0 1 * L 1 0 * L 2 2 + L 0 1 * L 1 2 * L 2 0 + L 0 2 * L 1 0 * L 2 1 - L 0 2 * L 1 1 * L 2 0)) = L 3 3 := by
    have h := congrFun (congrFun hadj 3) 3
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have g00 : (1) * L 0 0 * L 0 0 + (-1) * L 1 0 * L 1 0 + (-1) * L 2 0 * L 2 0 + (-1) * L 3 0 * L 3 0 = 1 := by
    have h := congrFun (congrFun hG 0) 0
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g01 : (1) * L 0 0 * L 0 1 + (-1) * L 1 0 * L 1 1 + (-1) * L 2 0 * L 2 1 + (-1) * L 3 0 * L 3 1 = 0 := by
    have h := congrFun (congrFun hG 0) 1
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g02 : (1) * L 0 0 * L 0 2 + (-1) * L 1 0 * L 1 2 + (-1) * L 2 0 * L 2 2 + (-1) * L 3 0 * L 3 2 = 0 := by
    have h := congrFun (congrFun hG 0) 2
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g03 : (1) * L 0 0 * L 0 3 + (-1) * L 1 0 * L 1 3 + (-1) * L 2 0 * L 2 3 + (-1) * L 3 0 * L 3 3 = 0 := by
    have h := congrFun (congrFun hG 0) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g11 : (1) * L 0 1 * L 0 1 + (-1) * L 1 1 * L 1 1 + (-1) * L 2 1 * L 2 1 + (-1) * L 3 1 * L 3 1 = -1 := by
    have h := congrFun (congrFun hG 1) 1
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g12 : (1) * L 0 1 * L 0 2 + (-1) * L 1 1 * L 1 2 + (-1) * L 2 1 * L 2 2 + (-1) * L 3 1 * L 3 2 = 0 := by
    have h := congrFun (congrFun hG 1) 2
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g13 : (1) * L 0 1 * L 0 3 + (-1) * L 1 1 * L 1 3 + (-1) * L 2 1 * L 2 3 + (-1) * L 3 1 * L 3 3 = 0 := by
    have h := congrFun (congrFun hG 1) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g22 : (1) * L 0 2 * L 0 2 + (-1) * L 1 2 * L 1 2 + (-1) * L 2 2 * L 2 2 + (-1) * L 3 2 * L 3 2 = -1 := by
    have h := congrFun (congrFun hG 2) 2
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g23 : (1) * L 0 2 * L 0 3 + (-1) * L 1 2 * L 1 3 + (-1) * L 2 2 * L 2 3 + (-1) * L 3 2 * L 3 3 = 0 := by
    have h := congrFun (congrFun hG 2) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g33 : (1) * L 0 3 * L 0 3 + (-1) * L 1 3 * L 1 3 + (-1) * L 2 3 * L 2 3 + (-1) * L 3 3 * L 3 3 = -1 := by
    have h := congrFun (congrFun hG 3) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h00 : (1) * L 0 0 * L 0 0 + (-1) * L 0 1 * L 0 1 + (-1) * L 0 2 * L 0 2 + (-1) * L 0 3 * L 0 3 = 1 := by
    have h := congrFun (congrFun hH 0) 0
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h01 : (1) * L 0 0 * L 1 0 + (-1) * L 0 1 * L 1 1 + (-1) * L 0 2 * L 1 2 + (-1) * L 0 3 * L 1 3 = 0 := by
    have h := congrFun (congrFun hH 0) 1
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h02 : (1) * L 0 0 * L 2 0 + (-1) * L 0 1 * L 2 1 + (-1) * L 0 2 * L 2 2 + (-1) * L 0 3 * L 2 3 = 0 := by
    have h := congrFun (congrFun hH 0) 2
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h03 : (1) * L 0 0 * L 3 0 + (-1) * L 0 1 * L 3 1 + (-1) * L 0 2 * L 3 2 + (-1) * L 0 3 * L 3 3 = 0 := by
    have h := congrFun (congrFun hH 0) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h11 : (1) * L 1 0 * L 1 0 + (-1) * L 1 1 * L 1 1 + (-1) * L 1 2 * L 1 2 + (-1) * L 1 3 * L 1 3 = -1 := by
    have h := congrFun (congrFun hH 1) 1
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h12 : (1) * L 1 0 * L 2 0 + (-1) * L 1 1 * L 2 1 + (-1) * L 1 2 * L 2 2 + (-1) * L 1 3 * L 2 3 = 0 := by
    have h := congrFun (congrFun hH 1) 2
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h13 : (1) * L 1 0 * L 3 0 + (-1) * L 1 1 * L 3 1 + (-1) * L 1 2 * L 3 2 + (-1) * L 1 3 * L 3 3 = 0 := by
    have h := congrFun (congrFun hH 1) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h22 : (1) * L 2 0 * L 2 0 + (-1) * L 2 1 * L 2 1 + (-1) * L 2 2 * L 2 2 + (-1) * L 2 3 * L 2 3 = -1 := by
    have h := congrFun (congrFun hH 2) 2
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h23 : (1) * L 2 0 * L 3 0 + (-1) * L 2 1 * L 3 1 + (-1) * L 2 2 * L 3 2 + (-1) * L 2 3 * L 3 3 = 0 := by
    have h := congrFun (congrFun hH 2) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h33 : (1) * L 3 0 * L 3 0 + (-1) * L 3 1 * L 3 1 + (-1) * L 3 2 * L 3 2 + (-1) * L 3 3 * L 3 3 = -1 := by
    have h := congrFun (congrFun hH 3) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have j01_01 : L 0 0 * L 1 1 - (-L 1 0) * (-L 0 1) = (1) * (L 2 2 * L 3 3 - L 2 3 * L 3 2) := by
    linear_combination (-L 1 1) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e11 + (-L 0 1) * e01 + (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) * e10 + (1) * (L 2 2 * L 3 3 - L 2 3 * L 3 2) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (1) * (L 2 2 * L 3 3 - L 2 3 * L 3 2) * h00
  have j01_02 : L 0 0 * L 2 1 - (-L 2 0) * (-L 0 1) = (-1) * (L 1 2 * L 3 3 - L 1 3 * L 3 2) := by
    linear_combination (-L 2 1) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e12 + (-L 0 1) * e02 + ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) * e10 + (-1) * (L 1 2 * L 3 3 - L 1 3 * L 3 2) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 1 2 * L 3 3 - L 1 3 * L 3 2) * h00
  have j01_03 : L 0 0 * L 3 1 - (-L 3 0) * (-L 0 1) = (1) * (L 1 2 * L 2 3 - L 1 3 * L 2 2) := by
    linear_combination (-L 3 1) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e13 + (-L 0 1) * e03 + (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) * e10 + (1) * (L 1 2 * L 2 3 - L 1 3 * L 2 2) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (1) * (L 1 2 * L 2 3 - L 1 3 * L 2 2) * h00
  have j01_12 : (-L 1 0) * L 2 1 - (-L 2 0) * L 1 1 = (1) * (L 0 2 * L 3 3 - L 0 3 * L 3 2) := by
    linear_combination (-L 2 1) * e01 - (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) * e12 + L 1 1 * e02 + ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) * e11 + (1) * (L 0 2 * L 3 3 - L 0 3 * L 3 2) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (1) * (L 0 2 * L 3 3 - L 0 3 * L 3 2) * h00
  have j01_13 : (-L 1 0) * L 3 1 - (-L 3 0) * L 1 1 = (-1) * (L 0 2 * L 2 3 - L 0 3 * L 2 2) := by
    linear_combination (-L 3 1) * e01 - (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) * e13 + L 1 1 * e03 + (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) * e11 + (-1) * (L 0 2 * L 2 3 - L 0 3 * L 2 2) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 0 2 * L 2 3 - L 0 3 * L 2 2) * h00
  have j02_01 : L 0 0 * L 1 2 - (-L 1 0) * (-L 0 2) = (-1) * (L 2 1 * L 3 3 - L 2 3 * L 3 1) := by
    linear_combination (-L 1 2) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e21 + (-L 0 2) * e01 + (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) * e20 + (-1) * (L 2 1 * L 3 3 - L 2 3 * L 3 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 2 1 * L 3 3 - L 2 3 * L 3 1) * h00
  have j02_02 : L 0 0 * L 2 2 - (-L 2 0) * (-L 0 2) = (1) * (L 1 1 * L 3 3 - L 1 3 * L 3 1) := by
    linear_combination (-L 2 2) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e22 + (-L 0 2) * e02 + ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) * e20 + (1) * (L 1 1 * L 3 3 - L 1 3 * L 3 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (1) * (L 1 1 * L 3 3 - L 1 3 * L 3 1) * h00
  have j02_03 : L 0 0 * L 3 2 - (-L 3 0) * (-L 0 2) = (-1) * (L 1 1 * L 2 3 - L 1 3 * L 2 1) := by
    linear_combination (-L 3 2) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e23 + (-L 0 2) * e03 + (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) * e20 + (-1) * (L 1 1 * L 2 3 - L 1 3 * L 2 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 1 1 * L 2 3 - L 1 3 * L 2 1) * h00
  have j02_12 : (-L 1 0) * L 2 2 - (-L 2 0) * L 1 2 = (-1) * (L 0 1 * L 3 3 - L 0 3 * L 3 1) := by
    linear_combination (-L 2 2) * e01 - (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) * e22 + L 1 2 * e02 + ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) * e21 + (-1) * (L 0 1 * L 3 3 - L 0 3 * L 3 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 0 1 * L 3 3 - L 0 3 * L 3 1) * h00
  have j02_23 : (-L 2 0) * L 3 2 - (-L 3 0) * L 2 2 = (-1) * (L 0 1 * L 1 3 - L 0 3 * L 1 1) := by
    linear_combination (-L 3 2) * e02 - ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) * e23 + L 2 2 * e03 + (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) * e22 + (-1) * (L 0 1 * L 1 3 - L 0 3 * L 1 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 0 1 * L 1 3 - L 0 3 * L 1 1) * h00
  have j03_01 : L 0 0 * L 1 3 - (-L 1 0) * (-L 0 3) = (1) * (L 2 1 * L 3 2 - L 2 2 * L 3 1) := by
    linear_combination (-L 1 3) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e31 + (-L 0 3) * e01 + (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) * e30 + (1) * (L 2 1 * L 3 2 - L 2 2 * L 3 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (1) * (L 2 1 * L 3 2 - L 2 2 * L 3 1) * h00
  have j03_02 : L 0 0 * L 2 3 - (-L 2 0) * (-L 0 3) = (-1) * (L 1 1 * L 3 2 - L 1 2 * L 3 1) := by
    linear_combination (-L 2 3) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e32 + (-L 0 3) * e02 + ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) * e30 + (-1) * (L 1 1 * L 3 2 - L 1 2 * L 3 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 1 1 * L 3 2 - L 1 2 * L 3 1) * h00
  have j03_03 : L 0 0 * L 3 3 - (-L 3 0) * (-L 0 3) = (1) * (L 1 1 * L 2 2 - L 1 2 * L 2 1) := by
    linear_combination (-L 3 3) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e33 + (-L 0 3) * e03 + (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) * e30 + (1) * (L 1 1 * L 2 2 - L 1 2 * L 2 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (1) * (L 1 1 * L 2 2 - L 1 2 * L 2 1) * h00
  have j03_13 : (-L 1 0) * L 3 3 - (-L 3 0) * L 1 3 = (-1) * (L 0 1 * L 2 2 - L 0 2 * L 2 1) := by
    linear_combination (-L 3 3) * e01 - (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) * e33 + L 1 3 * e03 + (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) * e31 + (-1) * (L 0 1 * L 2 2 - L 0 2 * L 2 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 0 1 * L 2 2 - L 0 2 * L 2 1) * h00
  have j03_23 : (-L 2 0) * L 3 3 - (-L 3 0) * L 2 3 = (1) * (L 0 1 * L 1 2 - L 0 2 * L 1 1) := by
    linear_combination (-L 3 3) * e02 - ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) * e33 + L 2 3 * e03 + (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) * e32 + (1) * (L 0 1 * L 1 2 - L 0 2 * L 1 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (1) * (L 0 1 * L 1 2 - L 0 2 * L 1 1) * h00
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Nmat, hermOfVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Complex.star_def]
    refine ⟨?_, ?_⟩
    · linear_combination x 0 * ((-1) * g00 + (2) * g03 + (-1) * g11 + (-1) * g22 + (-1) * g33 + (-2) * h00 + (-2) * h03 + (-2) * j01_01 + (-2) * j01_13 + (-2) * j02_02 + (-2) * j02_23 + (-2) * j03_03) + x 1 * ((-2) * g01 + (2) * g13 + (2) * h01 + (2) * h13 + (-2) * j01_03 + (-2) * j02_12 + (-2) * j03_01 + (-2) * j03_13) + x 2 * ((-2) * g02 + (2) * g23 + (2) * h02 + (2) * h23 + (2) * j01_12 + (-2) * j02_03 + (-2) * j03_02 + (-2) * j03_23) + x 3 * ((-1) * g00 + (-2) * g03 + (1) * g11 + (1) * g22 + (3) * g33 + (2) * h00 + (2) * h03 + (-2) * h11 + (-2) * h22 + (2) * j01_01 + (2) * j01_13 + (2) * j02_02 + (2) * j02_23 + (-2) * j03_03)
    · linear_combination
  · simp [Nmat, hermOfVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Complex.star_def]
    refine ⟨?_, ?_⟩
    · linear_combination x 0 * ((2) * g01 + (-2) * h01 + (2) * j02_12 + (2) * j03_13) + x 1 * ((1) * g00 + (1) * g11 + (-1) * g22 + (-1) * g33 + (2) * h11 + (-2) * j01_01 + (2) * j02_02 + (2) * j03_03) + x 2 * ((2) * g12 + (2) * h12 + (-2) * j01_02 + (-2) * j02_01) + x 3 * ((2) * g13 + (2) * h13 + (-2) * j01_03 + (-2) * j03_01)
    · linear_combination x 0 * ((-2) * g02 + (2) * h02 + (2) * j01_12 + (-2) * j03_23) + x 1 * ((-2) * g12 + (-2) * h12 + (2) * j01_02 + (2) * j02_01) + x 2 * ((-1) * g00 + (1) * g11 + (-1) * g22 + (1) * g33 + (-2) * h22 + (-2) * j01_01 + (2) * j02_02 + (-2) * j03_03) + x 3 * ((-2) * g23 + (-2) * h23 + (2) * j02_03 + (2) * j03_02)
  · simp [Nmat, hermOfVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Complex.star_def]
    refine ⟨?_, ?_⟩
    · linear_combination x 0 * ((2) * g01 + (-2) * h01 + (2) * j02_12 + (2) * j03_13) + x 1 * ((1) * g00 + (1) * g11 + (-1) * g22 + (-1) * g33 + (2) * h11 + (-2) * j01_01 + (2) * j02_02 + (2) * j03_03) + x 2 * ((2) * g12 + (2) * h12 + (-2) * j01_02 + (-2) * j02_01) + x 3 * ((2) * g13 + (2) * h13 + (-2) * j01_03 + (-2) * j03_01)
    · linear_combination x 0 * ((2) * g02 + (-2) * h02 + (-2) * j01_12 + (2) * j03_23) + x 1 * ((2) * g12 + (2) * h12 + (-2) * j01_02 + (-2) * j02_01) + x 2 * ((1) * g00 + (-1) * g11 + (1) * g22 + (-1) * g33 + (2) * h22 + (2) * j01_01 + (-2) * j02_02 + (2) * j03_03) + x 3 * ((2) * g23 + (2) * h23 + (-2) * j02_03 + (-2) * j03_02)
  · simp [Nmat, hermOfVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Complex.star_def]
    refine ⟨?_, ?_⟩
    · linear_combination x 0 * ((-1) * g00 + (-2) * g03 + (-1) * g11 + (-1) * g22 + (-1) * g33 + (-2) * h00 + (2) * h03 + (-2) * j01_01 + (2) * j01_13 + (-2) * j02_02 + (2) * j02_23 + (-2) * j03_03) + x 1 * ((-2) * g01 + (-2) * g13 + (2) * h01 + (-2) * h13 + (2) * j01_03 + (-2) * j02_12 + (2) * j03_01 + (-2) * j03_13) + x 2 * ((-2) * g02 + (-2) * g23 + (2) * h02 + (-2) * h23 + (2) * j01_12 + (2) * j02_03 + (2) * j03_02 + (-2) * j03_23) + x 3 * ((1) * g00 + (-2) * g03 + (-1) * g11 + (-1) * g22 + (-3) * g33 + (-2) * h00 + (2) * h03 + (2) * h11 + (2) * h22 + (-2) * j01_01 + (2) * j01_13 + (-2) * j02_02 + (2) * j02_23 + (2) * j03_03)
    · linear_combination

/-! ## Surjectivity -/

theorem main_pos (L : Matrix (Fin 4) (Fin 4) ℝ) (hG : Lᵀ * eta * L = eta) (hdet : L.det = 1)
    (htr : 0 < L 0 0 + L 1 1 + L 2 2 + L 3 3) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ ∀ x, kappa A x = L *ᵥ x := by
  have hk := key L hG hdet
  set t := L 0 0 + L 1 1 + L 2 2 + L 3 3 with ht
  have g00 : L 0 0 * L 0 0 - L 1 0 * L 1 0 - L 2 0 * L 2 0 - L 3 0 * L 3 0 = 1 := by
    have h := congrFun (congrFun hG 0) 0
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have hm : minkowskiSq (L *ᵥ ![1, 0, 0, 0]) = 1 := by
    simp [minkowskiSq, minkowskiInner, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    linear_combination g00
  have hdN : Complex.normSq (Nmat L).det = 16 * t ^ 2 := by
    have h := congrArg Matrix.det (hk ![1, 0, 0, 0])
    rw [hermOfVec_e0, Matrix.mul_one, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_smul,
      det_hermOfVec, hm, Complex.star_def, Complex.mul_conj] at h
    have h3 : Complex.normSq (Nmat L).det = (4 * t) ^ 2 := by
      simp only [Fintype.card_fin, Complex.ofReal_one, mul_one] at h
      exact_mod_cast h
    linear_combination h3
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self ((Nmat L).det / 4)
  have hN4 : (Nmat L).det = 4 * (s * s) := by rw [← hs]; ring
  have hns : Complex.normSq s = t := by
    rw [hN4, Complex.normSq_mul, Complex.normSq_mul] at hdN
    have h4 : Complex.normSq 4 = 16 := by norm_num [Complex.normSq_apply]
    rw [h4] at hdN
    have hnn := Complex.normSq_nonneg s
    have hprod : (Complex.normSq s - t) * (Complex.normSq s + t) = 0 := by
      linear_combination hdN / 16
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · linarith
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, Complex.normSq_zero] at hns
    linarith
  have ht0 : t ≠ 0 := ne_of_gt htr
  refine ⟨(2 * s)⁻¹ • Nmat L, ?_, ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin, hN4]
    field_simp
    ring
  · apply kappa_of_herm
    intro x
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hk x, smul_smul]
    have hc : (2 * s)⁻¹ * star ((2 * s)⁻¹) * ((4 * t : ℝ) : ℂ) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_inv, Complex.normSq_mul, hns]
      have h2 : Complex.normSq 2 = 4 := by norm_num [Complex.normSq_apply]
      rw [h2]
      push_cast
      field_simp
    rw [hc, one_smul]

theorem diag_lorentz (d : Fin 4 → ℝ) (hd : ∀ i, d i * d i = 1) :
    (Matrix.diagonal d)ᵀ * eta * Matrix.diagonal d = eta := by
  rw [Matrix.diagonal_transpose, eta, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  calc d i * ![(1 : ℝ), -1, -1, -1] i * d i = ![(1 : ℝ), -1, -1, -1] i * (d i * d i) := by ring
    _ = ![(1 : ℝ), -1, -1, -1] i := by rw [hd i, mul_one]

theorem diag_sq (d : Fin 4 → ℝ) (hd : ∀ i, d i * d i = 1) :
    Matrix.diagonal d * Matrix.diagonal d = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact hd i

theorem reduce (L D : Matrix (Fin 4) (Fin 4) ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P.det = 1)
    (hPD : ∀ x, P * hermOfVec x * Pᴴ = hermOfVec (D *ᵥ x)) (hDD : D * D = 1)
    (hG : Lᵀ * eta * L = eta) (hD : Dᵀ * eta * D = eta) (hdet : L.det = 1) (hDdet : D.det = 1)
    (htr : 0 < (L * D) 0 0 + (L * D) 1 1 + (L * D) 2 2 + (L * D) 3 3) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ ∀ x, kappa A x = L *ᵥ x := by
  have hG' : (L * D)ᵀ * eta * (L * D) = eta := by
    rw [Matrix.transpose_mul]
    calc Dᵀ * Lᵀ * eta * (L * D) = Dᵀ * (Lᵀ * eta * L) * D := by simp only [Matrix.mul_assoc]
      _ = eta := by rw [hG, hD]
  have hdet' : (L * D).det = 1 := by rw [Matrix.det_mul, hdet, hDdet, one_mul]
  obtain ⟨A', hA', hA'x⟩ := main_pos (L * D) hG' hdet' htr
  refine ⟨A' * P, by rw [Matrix.det_mul, hA', hP, one_mul], fun x => ?_⟩
  rw [← kappa_kappa, kappa_of_herm P D hPD, hA'x, Matrix.mulVec_mulVec, Matrix.mul_assoc, hDD,
    Matrix.mul_one]

theorem herm_P1 (x : Fin 4 → ℝ) :
    !![0, Complex.I; Complex.I, 0] * hermOfVec x * (!![0, Complex.I; Complex.I, 0])ᴴ =
      hermOfVec (Matrix.diagonal ![1, 1, -1, -1] *ᵥ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermOfVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.diagonal,
      Complex.star_def] <;> (try refine ⟨?_, ?_⟩) <;> ring

theorem herm_P2 (x : Fin 4 → ℝ) :
    !![0, 1; -1, 0] * hermOfVec x * (!![(0 : ℂ), 1; -1, 0])ᴴ =
      hermOfVec (Matrix.diagonal ![1, -1, 1, -1] *ᵥ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermOfVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.diagonal,
      Complex.star_def] <;> (try refine ⟨?_, ?_⟩) <;> ring

theorem herm_P3 (x : Fin 4 → ℝ) :
    !![Complex.I, 0; 0, -Complex.I] * hermOfVec x * (!![Complex.I, 0; 0, -Complex.I])ᴴ =
      hermOfVec (Matrix.diagonal ![1, -1, -1, 1] *ᵥ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermOfVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.diagonal,
      Complex.star_def] <;> (try refine ⟨?_, ?_⟩) <;> ring


theorem surj' (L : Matrix (Fin 4) (Fin 4) ℝ) (hG : Lᵀ * eta * L = eta) (hdet : L.det = 1)
    (h00 : 0 < L 0 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ ∀ x, kappa A x = L *ᵥ x := by
  by_cases h0 : 0 < L 0 0 + L 1 1 + L 2 2 + L 3 3
  · exact main_pos L hG hdet h0
  by_cases h1 : 0 < L 0 0 + L 1 1 - L 2 2 - L 3 3
  · refine reduce L (Matrix.diagonal ![1, 1, -1, -1]) _ (by simp [Matrix.det_fin_two])
      herm_P1 (diag_sq _ (by intro i; fin_cases i <;> norm_num)) hG
      (diag_lorentz _ (by intro i; fin_cases i <;> norm_num)) hdet
      (by simp [Matrix.det_diagonal, Fin.prod_univ_four]) ?_
    simp [Matrix.mul_diagonal]
    linarith
  by_cases h2 : 0 < L 0 0 - L 1 1 + L 2 2 - L 3 3
  · refine reduce L (Matrix.diagonal ![1, -1, 1, -1]) _ (by simp [Matrix.det_fin_two])
      herm_P2 (diag_sq _ (by intro i; fin_cases i <;> norm_num)) hG
      (diag_lorentz _ (by intro i; fin_cases i <;> norm_num)) hdet
      (by simp [Matrix.det_diagonal, Fin.prod_univ_four]) ?_
    simp [Matrix.mul_diagonal]
    linarith
  by_cases h3 : 0 < L 0 0 - L 1 1 - L 2 2 + L 3 3
  · refine reduce L (Matrix.diagonal ![1, -1, -1, 1]) _ (by simp [Matrix.det_fin_two])
      herm_P3 (diag_sq _ (by intro i; fin_cases i <;> norm_num)) hG
      (diag_lorentz _ (by intro i; fin_cases i <;> norm_num)) hdet
      (by simp [Matrix.det_diagonal, Fin.prod_univ_four]) ?_
    simp [Matrix.mul_diagonal]
    linarith
  exfalso
  linarith

end ChatterjeeQFTKappa

namespace SpinRepBuild

open Matrix Filter Topology SpinStatistics
open scoped ComplexOrder

/-! ## Unipotents of `SL(2,C)` and their images, the null rotations -/

def U2 (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, z; 0, 1]

def L2 (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; z, 1]

noncomputable def NU (p q : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 + (p ^ 2 + q ^ 2) / 2, p, -q, -((p ^ 2 + q ^ 2) / 2);
     p, 1, 0, -p;
     -q, 0, 1, q;
     (p ^ 2 + q ^ 2) / 2, p, -q, 1 - (p ^ 2 + q ^ 2) / 2]

noncomputable def NL (p q : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 + (p ^ 2 + q ^ 2) / 2, p, q, (p ^ 2 + q ^ 2) / 2;
     p, 1, 0, p;
     q, 0, 1, q;
     -((p ^ 2 + q ^ 2) / 2), -p, -q, 1 - (p ^ 2 + q ^ 2) / 2]

noncomputable def Bst (s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(s + s⁻¹) / 2, 0, 0, (s - s⁻¹) / 2;
     0, 1, 0, 0;
     0, 0, 1, 0;
     (s - s⁻¹) / 2, 0, 0, (s + s⁻¹) / 2]

theorem kappa_U2 (z : ℂ) (x : Fin 4 → ℝ) :
    ChatterjeeQFT.kappa (U2 z) x = NU z.re z.im *ᵥ x := by
  refine ChatterjeeQFTKappa.kappa_of_herm _ _ (fun x => ?_) x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U2, NU, ChatterjeeQFT.hermOfVec, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Complex.star_def] <;> (try refine ⟨?_, ?_⟩) <;>
    (try simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]) <;> ring

theorem kappa_L2 (z : ℂ) (x : Fin 4 → ℝ) :
    ChatterjeeQFT.kappa (L2 z) x = NL z.re z.im *ᵥ x := by
  refine ChatterjeeQFTKappa.kappa_of_herm _ _ (fun x => ?_) x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [L2, NL, ChatterjeeQFT.hermOfVec, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Complex.star_def] <;> (try refine ⟨?_, ?_⟩) <;>
    (try simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]) <;> ring

theorem sl2_decomp (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    ∃ w x c y : ℂ, A = L2 w * U2 x * L2 c * U2 y := by
  rw [Matrix.det_fin_two] at hA
  by_cases hc : A 1 0 = 0
  · have ha : A 0 0 ≠ 0 := by
      intro h
      rw [h, hc] at hA
      simp at hA
    simp only [hc, mul_zero, sub_zero] at hA
    refine ⟨1, (A 0 0 - 1) / (-(A 0 0)), -(A 0 0), (A 1 1 - A 0 1 - 1) / (-(A 0 0)), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L2, U2, Matrix.mul_apply, Fin.sum_univ_two, hc] <;> field_simp <;>
      first
        | ring1
        | linear_combination hA
        | linear_combination -hA
        | linear_combination (A 0 0) * hA
        | linear_combination -(A 0 0) * hA
  · refine ⟨0, (A 0 0 - 1) / A 1 0, A 1 0, (A 1 1 - 1) / A 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L2, U2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
      first
        | ring1
        | linear_combination hA
        | linear_combination -hA
        | linear_combination (A 1 0) * hA
        | linear_combination -(A 1 0) * hA

/-! ## The restricted Lorentz group is closed under products -/

theorem eta_sq : minkowskiMetric * minkowskiMetric = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  rw [minkowskiMetric, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

theorem row_rel (A : Matrix (Fin 4) (Fin 4) ℝ) (h : Aᵀ * minkowskiMetric * A = minkowskiMetric) :
    A * minkowskiMetric * Aᵀ = minkowskiMetric := by
  have hleft : (minkowskiMetric * Aᵀ * minkowskiMetric) * A = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, h, eta_sq]
  have hright : A * (minkowskiMetric * Aᵀ * minkowskiMetric) = 1 := mul_eq_one_comm.mp hleft
  calc A * minkowskiMetric * Aᵀ
      = A * (minkowskiMetric * Aᵀ * minkowskiMetric) * minkowskiMetric := by
        simp only [Matrix.mul_assoc, eta_sq, Matrix.mul_one]
    _ = minkowskiMetric := by rw [hright, Matrix.one_mul]

theorem key_ineq (a0 a1 a2 a3 b0 b1 b2 b3 : ℝ)
    (ha : a0 * a0 - a1 * a1 - a2 * a2 - a3 * a3 = 1)
    (hb : b0 * b0 - b1 * b1 - b2 * b2 - b3 * b3 = 1) (ha0 : 1 ≤ a0) (hb0 : 1 ≤ b0) :
    1 ≤ a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 := by
  set d := a1 * b1 + a2 * b2 + a3 * b3 with hd
  have hP : 1 ≤ a0 * b0 := by nlinarith
  by_cases h : 1 - d ≤ 0
  · nlinarith
  push Not at h
  have hid : (a0 * b0) ^ 2 - (1 - d) ^ 2 =
      (a1 + b1) ^ 2 + (a2 + b2) ^ 2 + (a3 + b3) ^ 2 + (a1 * b2 - a2 * b1) ^ 2 +
        (a1 * b3 - a3 * b1) ^ 2 + (a2 * b3 - a3 * b2) ^ 2 := by
    rw [hd]
    linear_combination (b0 ^ 2) * ha + (1 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2) * hb
  have hsq : (1 - d) ^ 2 ≤ (a0 * b0) ^ 2 := by
    nlinarith [sq_nonneg (a1 + b1), sq_nonneg (a2 + b2), sq_nonneg (a3 + b3),
      sq_nonneg (a1 * b2 - a2 * b1), sq_nonneg (a1 * b3 - a3 * b1), sq_nonneg (a2 * b3 - a3 * b2)]
  nlinarith

theorem mul_mem' {A B : Matrix (Fin 4) (Fin 4) ℝ} (hA : A ∈ restrictedLorentzSet)
    (hB : B ∈ restrictedLorentzSet) : A * B ∈ restrictedLorentzSet := by
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hA1' : Aᵀ * minkowskiMetric * A = minkowskiMetric := hA1
  have hB1' : Bᵀ * minkowskiMetric * B = minkowskiMetric := hB1
  refine ⟨?_, ?_, ?_⟩
  · show (A * B)ᵀ * minkowskiMetric * (A * B) = minkowskiMetric
    rw [Matrix.transpose_mul]
    calc Bᵀ * Aᵀ * minkowskiMetric * (A * B) = Bᵀ * (Aᵀ * minkowskiMetric * A) * B := by
          simp only [Matrix.mul_assoc]
      _ = minkowskiMetric := by rw [hA1', hB1']
  · rw [Matrix.det_mul, hA2, hB2, one_mul]
  · have hr := congrFun (congrFun (row_rel A hA1') 0) 0
    have hc := congrFun (congrFun hB1' 0) 0
    simp [minkowskiMetric, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at hr hc
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    have := key_ineq (A 0 0) (A 0 1) (A 0 2) (A 0 3) (B 0 0) (B 1 0) (B 2 0) (B 3 0)
      (by linear_combination hr) (by linear_combination hc) hA3 hB3
    linarith

theorem one_mem' : (1 : Matrix (Fin 4) (Fin 4) ℝ) ∈ restrictedLorentzSet := by
  refine ⟨?_, ?_, ?_⟩
  · show (1 : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * minkowskiMetric * 1 = minkowskiMetric
    simp
  · simp
  · simp

/-! ## Membership of the explicit matrices -/

theorem NU_mem (p q : ℝ) : NU p q ∈ restrictedLorentzSet := by
  refine ⟨?_, ?_, ?_⟩
  · show (NU p q)ᵀ * minkowskiMetric * NU p q = minkowskiMetric
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [NU, minkowskiMetric, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] <;> ring
  · rw [Matrix.det_succ_row_zero]
    simp [NU, Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]
    ring
  · simp [NU]
    positivity

theorem NL_mem (p q : ℝ) : NL p q ∈ restrictedLorentzSet := by
  refine ⟨?_, ?_, ?_⟩
  · show (NL p q)ᵀ * minkowskiMetric * NL p q = minkowskiMetric
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [NL, minkowskiMetric, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] <;> ring
  · rw [Matrix.det_succ_row_zero]
    simp [NL, Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]
    ring
  · simp [NL]
    positivity

theorem Bst_mem (s : ℝ) (hs : 0 < s) : Bst s ∈ restrictedLorentzSet := by
  have hs0 : s ≠ 0 := hs.ne'
  refine ⟨?_, ?_, ?_⟩
  · show (Bst s)ᵀ * minkowskiMetric * Bst s = minkowskiMetric
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Bst, minkowskiMetric, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] <;>
      field_simp <;> ring
  · rw [Matrix.det_succ_row_zero]
    simp [Bst, Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]
    field_simp
    ring
  · have h2 : s + s⁻¹ - 2 = (s - 1) ^ 2 / s := by
      field_simp
      ring
    have h3 : 0 ≤ (s - 1) ^ 2 / s := div_nonneg (sq_nonneg _) hs.le
    show 1 ≤ (Bst s) 0 0
    simp [Bst]
    linarith

theorem Bst_NU (s : ℝ) (hs : 0 < s) (p q : ℝ) :
    Bst s * NU p q = NU (s * p) (s * q) * Bst s := by
  have hs0 : s ≠ 0 := hs.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Bst, NU, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring

theorem Bst_NL (s : ℝ) (hs : 0 < s) (p q : ℝ) :
    Bst s⁻¹ * NL p q = NL (s * p) (s * q) * Bst s⁻¹ := by
  have hs0 : s ≠ 0 := hs.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Bst, NL, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring

theorem NU_cont (p q : ℝ) : Continuous (fun s : ℝ => NU (s * p) (s * q)) := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [NU] <;> fun_prop

theorem NL_cont (p q : ℝ) : Continuous (fun s : ℝ => NL (s * p) (s * q)) := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [NL] <;> fun_prop

theorem NU_zero (p q : ℝ) : NU (0 * p) (0 * q) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [NU, Matrix.one_apply]

theorem NL_zero (p q : ℝ) : NL (0 * p) (0 * q) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [NL, Matrix.one_apply]

/-! ## Unitary matrices with trace `n` -/

theorem unitary_eq_one_of_trace {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (h : (U : Matrix (Fin n) (Fin n) ℂ).trace = n) : U = 1 := by
  have hU : star (U : Matrix (Fin n) (Fin n) ℂ) * U = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  rw [Matrix.star_eq_conjTranspose] at hU
  have ht : (((U : Matrix (Fin n) (Fin n) ℂ) - 1)ᴴ * ((U : Matrix (Fin n) (Fin n) ℂ) - 1)).trace
      = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, hU, Matrix.mul_one, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_sub, Matrix.trace_conjTranspose, h, Matrix.trace_one]
    simp
  rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff, sub_eq_zero] at ht
  exact Subtype.ext ht

/-! ## Null rotations act trivially -/

theorem rho_one {n : ℕ} (ρ : Matrix (Fin 4) (Fin 4) ℝ → Matrix.unitaryGroup (Fin n) ℂ)
    (hmul : ∀ A ∈ restrictedLorentzSet, ∀ B ∈ restrictedLorentzSet, ρ (A * B) = ρ A * ρ B) :
    ρ 1 = 1 := by
  have h := hmul 1 one_mem' 1 one_mem'
  rw [Matrix.mul_one] at h
  simpa using h

theorem conj_limit {n : ℕ} (ρ : Matrix (Fin 4) (Fin 4) ℝ → Matrix.unitaryGroup (Fin n) ℂ)
    (hmul : ∀ A ∈ restrictedLorentzSet, ∀ B ∈ restrictedLorentzSet, ρ (A * B) = ρ A * ρ B)
    (hcont : ContinuousOn ρ restrictedLorentzSet)
    (N : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (hNc : Continuous N) (hN0 : N 0 = 1)
    (hNG : ∀ s, N s ∈ restrictedLorentzSet)
    (hconj : ∀ s : ℝ, 0 < s → ∃ h ∈ restrictedLorentzSet, h * N 1 = N s * h) :
    ρ (N 1) = 1 := by
  let g : ℝ → ℂ := fun s => ((ρ (N s) : Matrix (Fin n) (Fin n) ℂ)).trace
  have hgc : Continuous g := by
    have h1 : Continuous (fun s => ρ (N s)) := hcont.comp_continuous hNc hNG
    exact (continuous_subtype_val.comp h1).matrix_trace
  have hconst : ∀ s : ℝ, 0 < s → g s = g 1 := by
    intro s hs
    obtain ⟨h, hh, hcomm⟩ := hconj s hs
    have e1 := hmul h hh (N 1) (hNG 1)
    have e2 := hmul (N s) (hNG s) h hh
    rw [hcomm, e2] at e1
    have e3 := congrArg (fun V : Matrix.unitaryGroup (Fin n) ℂ => (V : Matrix (Fin n) (Fin n) ℂ)) e1
    simp only [Submonoid.coe_mul] at e3
    have hH : (ρ h : Matrix (Fin n) (Fin n) ℂ) * star (ρ h : Matrix (Fin n) (Fin n) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (ρ h).2
    have hHs : star (ρ h : Matrix (Fin n) (Fin n) ℂ) * (ρ h : Matrix (Fin n) (Fin n) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp (ρ h).2
    show ((ρ (N s) : Matrix (Fin n) (Fin n) ℂ)).trace = ((ρ (N 1) : Matrix (Fin n) (Fin n) ℂ)).trace
    calc ((ρ (N s) : Matrix (Fin n) (Fin n) ℂ)).trace
        = ((ρ (N s) : Matrix (Fin n) (Fin n) ℂ) * (ρ h : Matrix (Fin n) (Fin n) ℂ) *
            star (ρ h : Matrix (Fin n) (Fin n) ℂ)).trace := by
          rw [Matrix.mul_assoc, hH, Matrix.mul_one]
      _ = ((ρ h : Matrix (Fin n) (Fin n) ℂ) * (ρ (N 1) : Matrix (Fin n) (Fin n) ℂ) *
            star (ρ h : Matrix (Fin n) (Fin n) ℂ)).trace := by rw [e3]
      _ = (star (ρ h : Matrix (Fin n) (Fin n) ℂ) * ((ρ h : Matrix (Fin n) (Fin n) ℂ) *
            (ρ (N 1) : Matrix (Fin n) (Fin n) ℂ))).trace := Matrix.trace_mul_comm _ _
      _ = ((ρ (N 1) : Matrix (Fin n) (Fin n) ℂ)).trace := by
          rw [← Matrix.mul_assoc, hHs, Matrix.one_mul]
  have hg0 : g 0 = n := by
    show ((ρ (N 0) : Matrix (Fin n) (Fin n) ℂ)).trace = n
    rw [hN0, rho_one ρ hmul]
    simp
  have hlim1 : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := (hgc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto g (𝓝[>] 0) (𝓝 (g 1)) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => (hconst s hs).symm)
  have heq : g 1 = g 0 := tendsto_nhds_unique hlim2 hlim1
  exact unitary_eq_one_of_trace _ (by rw [← hg0, ← heq])

theorem NU_trivial {n : ℕ} (ρ : Matrix (Fin 4) (Fin 4) ℝ → Matrix.unitaryGroup (Fin n) ℂ)
    (hmul : ∀ A ∈ restrictedLorentzSet, ∀ B ∈ restrictedLorentzSet, ρ (A * B) = ρ A * ρ B)
    (hcont : ContinuousOn ρ restrictedLorentzSet) (p q : ℝ) : ρ (NU p q) = 1 := by
  have h := conj_limit ρ hmul hcont (fun s => NU (s * p) (s * q)) (NU_cont p q) (NU_zero p q)
    (fun s => NU_mem _ _) (fun s hs => ⟨Bst s, Bst_mem s hs, by
      show Bst s * NU (1 * p) (1 * q) = NU (s * p) (s * q) * Bst s
      rw [one_mul, one_mul]
      exact Bst_NU s hs p q⟩)
  simpa using h

theorem NL_trivial {n : ℕ} (ρ : Matrix (Fin 4) (Fin 4) ℝ → Matrix.unitaryGroup (Fin n) ℂ)
    (hmul : ∀ A ∈ restrictedLorentzSet, ∀ B ∈ restrictedLorentzSet, ρ (A * B) = ρ A * ρ B)
    (hcont : ContinuousOn ρ restrictedLorentzSet) (p q : ℝ) : ρ (NL p q) = 1 := by
  have h := conj_limit ρ hmul hcont (fun s => NL (s * p) (s * q)) (NL_cont p q) (NL_zero p q)
    (fun s => NL_mem _ _) (fun s hs => ⟨Bst s⁻¹, Bst_mem s⁻¹ (inv_pos.mpr hs), by
      show Bst s⁻¹ * NL (1 * p) (1 * q) = NL (s * p) (s * q) * Bst s⁻¹
      rw [one_mul, one_mul]
      exact Bst_NL s hs p q⟩)
  simpa using h

/-! ## Assembly -/

theorem Lambda_eq (Λ : Matrix (Fin 4) (Fin 4) ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ x, ChatterjeeQFT.kappa A x = Λ *ᵥ x) (w x c y : ℂ)
    (hAe : A = L2 w * U2 x * L2 c * U2 y) :
    Λ = NL w.re w.im * NU x.re x.im * NL c.re c.im * NU y.re y.im := by
  have hv : ∀ v, Λ *ᵥ v = (NL w.re w.im * NU x.re x.im * NL c.re c.im * NU y.re y.im) *ᵥ v := by
    intro v
    rw [← hA, hAe, ← ChatterjeeQFTKappa.kappa_kappa, ← ChatterjeeQFTKappa.kappa_kappa,
      ← ChatterjeeQFTKappa.kappa_kappa]
    simp only [kappa_U2, kappa_L2, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem main {n : ℕ} (ρ : Matrix (Fin 4) (Fin 4) ℝ → Matrix.unitaryGroup (Fin n) ℂ)
    (hmul : ∀ A ∈ restrictedLorentzSet, ∀ B ∈ restrictedLorentzSet, ρ (A * B) = ρ A * ρ B)
    (hcont : ContinuousOn ρ restrictedLorentzSet) :
    ∀ Λ ∈ restrictedLorentzSet, ρ Λ = 1 := by
  intro Λ hΛ
  obtain ⟨hL, hdet, h00⟩ := hΛ
  obtain ⟨A, hAdet, hA⟩ := ChatterjeeQFTKappa.surj' Λ hL hdet (by linarith)
  obtain ⟨w, x, c, y, hAe⟩ := sl2_decomp A hAdet
  rw [Lambda_eq Λ A hA w x c y hAe,
    hmul _ (mul_mem' (mul_mem' (NL_mem _ _) (NU_mem _ _)) (NL_mem _ _)) _ (NU_mem _ _),
    hmul _ (mul_mem' (NL_mem _ _) (NU_mem _ _)) _ (NL_mem _ _),
    hmul _ (NL_mem _ _) _ (NU_mem _ _), NU_trivial ρ hmul hcont, NU_trivial ρ hmul hcont,
    NL_trivial ρ hmul hcont, NL_trivial ρ hmul hcont]
  simp

end SpinRepBuild

open SpinStatistics in
theorem solution (n : ℕ)
    (ρ : Matrix (Fin 4) (Fin 4) ℝ → Matrix.unitaryGroup (Fin n) ℂ)
    (hmul : ∀ A ∈ restrictedLorentzSet, ∀ B ∈ restrictedLorentzSet,
      ρ (A * B) = ρ A * ρ B)
    (hcont : ContinuousOn ρ restrictedLorentzSet) :
    ∀ Λ ∈ restrictedLorentzSet, ρ Λ = 1 := by
  exact SpinRepBuild.main ρ hmul hcont
