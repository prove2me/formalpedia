-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P53.fidelityTensorMultiplicativity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:59:31.04499+00:00
-- url     : https://prove2.me/submissions/de3d5641-0e57-4bf3-8fe5-134146f134c6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

open scoped Matrix ComplexOrder MatrixOrder Kronecker

lemma g53h_sqrt_unique {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hB : B.PosSemidef) (h : B * B = A) : cfc Real.sqrt A = B := by
  have hA : A.PosSemidef := by
    rw [← h]; have := Matrix.posSemidef_conjTranspose_mul_self B; rwa [hB.1.eq] at this
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_unique h hB.nonneg

lemma g53h_sqrt_psd {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    (cfc Real.sqrt A).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun x _ => Real.sqrt_nonneg x)

lemma g53h_sqrt_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma g53h_sqrt_kron {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    cfc Real.sqrt (A ⊗ₖ B) = cfc Real.sqrt A ⊗ₖ cfc Real.sqrt B := by
  apply g53h_sqrt_unique ((g53h_sqrt_psd A).kronecker (g53h_sqrt_psd B))
  rw [← Matrix.mul_kronecker_mul, g53h_sqrt_sq hA, g53h_sqrt_sq hB]

lemma g53h_M_psd {k : Type*} [Fintype k] [DecidableEq k] (X Y : Matrix k k ℂ) (hY : Y.PosSemidef) :
    (cfc Real.sqrt X * Y * cfc Real.sqrt X).PosSemidef := by
  have := hY.conjTranspose_mul_mul_same (cfc Real.sqrt X)
  rwa [(g53h_sqrt_psd X).1.eq] at this

lemma g53h_rootFid_kron {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A C : Matrix m m ℂ} {B D : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hC : C.PosSemidef) (hD : D.PosSemidef) :
    QAlgorithms.rootFidelity (Matrix.kronecker A B) (Matrix.kronecker C D) =
      QAlgorithms.rootFidelity A C * QAlgorithms.rootFidelity B D := by
  show QAlgorithms.rootFidelity (A ⊗ₖ B) (C ⊗ₖ D) = _
  unfold QAlgorithms.rootFidelity
  rw [g53h_sqrt_kron hA hB, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    g53h_sqrt_kron (g53h_M_psd A C hC) (g53h_M_psd B D hD), Matrix.trace_kronecker]
  have h1 := (g53h_sqrt_psd (cfc Real.sqrt A * C * cfc Real.sqrt A)).trace_nonneg
  have h2 := (g53h_sqrt_psd (cfc Real.sqrt B * D * cfc Real.sqrt B)).trace_nonneg
  rw [Complex.mul_re, (Complex.nonneg_iff.1 h1).2.symm, (Complex.nonneg_iff.1 h2).2.symm]
  ring

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.3, Eq.(3): the invoked background multiplicativity identity for
squared Uhlmann fidelity, with the tensor factors on positive finite dimensions. -/
theorem solution {N0 N1 : ℕ} (hN0 : 0 < N0) (hN1 : 0 < N1)
    (rho0 psi0 : Matrix (Fin N0) (Fin N0) ℂ)
    (rho1 psi1 : Matrix (Fin N1) (Fin N1) ℂ)
    (hrho0 : IsDensityMatrix rho0) (hpsi0 : IsDensityMatrix psi0)
    (hrho1 : IsDensityMatrix rho1) (hpsi1 : IsDensityMatrix psi1) :
    fidelity (Matrix.kronecker rho0 rho1) (Matrix.kronecker psi0 psi1) =
      fidelity rho0 psi0 * fidelity rho1 psi1 := by
  unfold fidelity
  rw [g53h_rootFid_kron hrho0.1 hrho1.1 hpsi0.1 hpsi1.1]
  ring



end

