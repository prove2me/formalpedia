-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P48.pure_output_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T10:11:12.941061+00:00
-- url     : https://prove2.me/submissions/a6d483fa-aec0-4101-812d-3c9f02016c22

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

theorem g68q_asc_map {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (Finset.univ : Finset (Fin (Fintype.card ι))).val.map (ascEigenvalues H) =
      (Finset.univ : Finset (Fin (Fintype.card ι))).val.map hH.eigenvalues₀ := by
  unfold ascEigenvalues
  rw [dif_pos hH]
  have h : (Finset.univ : Finset (Fin (Fintype.card ι))).val.map Fin.revPerm = Finset.univ.val := by
    have := congrArg Finset.val (Finset.map_univ_equiv (Fin.revPerm (n := Fintype.card ι)))
    rw [Finset.map_val] at this
    exact this
  rw [show (fun k => hH.eigenvalues₀ (Fin.rev k)) = hH.eigenvalues₀ ∘ Fin.revPerm from rfl,
    ← Multiset.map_map, h]

open Polynomial in
theorem g68q_roots_filter {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (nonzeroSpectrum H).map (fun x : ℝ => (x : ℂ)) = H.charpoly.roots.filter (fun z => z ≠ 0) := by
  rw [hH.roots_charpoly_eq_eigenvalues₀, nonzeroSpectrum, g68q_asc_map H hH, Multiset.filter_map,
    Multiset.filter_map, Multiset.map_map]
  congr 1
  apply Multiset.filter_congr
  intro x _
  simp

open Polynomial in
theorem g68q_filter_roots (p q : ℂ[X]) (hp : p ≠ 0) (hq : q ≠ 0) (k l : ℕ)
    (h : X ^ k * p = X ^ l * q) : p.roots.filter (fun z => z ≠ 0) = q.roots.filter (fun z => z ≠ 0) := by
  have h2 := congrArg (fun r : ℂ[X] => r.roots.filter (fun z => z ≠ 0)) h
  rw [roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hp), roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hq),
    roots_X_pow, roots_X_pow, Multiset.filter_add, Multiset.filter_add] at h2
  have h0 : ∀ n : ℕ, (n • ({0} : Multiset ℂ)).filter (fun z => z ≠ 0) = 0 := by
    intro n; rw [Multiset.filter_eq_nil]; intro a ha; rw [Multiset.mem_nsmul] at ha; simpa using ha.2
  simpa [h0] using h2

theorem g68q_spec_eq {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (H1 : Matrix m m ℂ) (H2 : Matrix n n ℂ) (h1 : H1.IsHermitian) (h2 : H2.IsHermitian) (k l : ℕ)
    (h : Polynomial.X ^ k * H1.charpoly = Polynomial.X ^ l * H2.charpoly) :
    nonzeroSpectrum H1 = nonzeroSpectrum H2 := by
  apply Multiset.map_injective (f := fun x : ℝ => (x : ℂ)) Complex.ofReal_injective
  rw [g68q_roots_filter H1 h1, g68q_roots_filter H2 h2]
  exact g68q_filter_roots _ _ (Matrix.charpoly_monic _).ne_zero (Matrix.charpoly_monic _).ne_zero k l h

theorem solution [Nonempty A] (V : Matrix (B × C) A ℂ) (psi : EuclideanSpace ℂ A) :
    (receiverChannel V (pureDensity psi)).IsHermitian ∧
    (complementaryChannel V (pureDensity psi)).IsHermitian ∧
    nonzeroSpectrum (receiverChannel V (pureDensity psi)) =
      nonzeroSpectrum (complementaryChannel V (pureDensity psi)) := by
  set w : B × C → ℂ := V *ᵥ (fun a => psi a) with hw
  set X : Matrix B C ℂ := Matrix.of fun b c => w (b, c) with hX
  have hP : V * pureDensity psi * Vᴴ = Matrix.vecMulVec w (star w) := by
    have : pureDensity psi = Matrix.vecMulVec (fun a => psi a) (star (fun a => psi a)) := by
      ext i j; simp [pureDensity, Matrix.vecMulVec_apply]
    rw [this, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose, star_star]
  have hR : receiverChannel V (pureDensity psi) = X * Xᴴ := by
    ext b b'
    simp only [receiverChannel, traceRight, hP]
    simp [ Matrix.mul_apply, Matrix.vecMulVec_apply, hX]
  have hC : complementaryChannel V (pureDensity psi) = (Xᴴ * X)ᵀ := by
    ext c c'
    simp only [complementaryChannel, traceLeft, hP]
    simp [ Matrix.mul_apply, Matrix.vecMulVec_apply, hX, mul_comm]
  have hh1 : (X * Xᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self X
  have hh2 : ((Xᴴ * X)ᵀ).IsHermitian := (Matrix.isHermitian_conjTranspose_mul_self X).transpose
  rw [hR, hC]
  refine ⟨hh1, hh2, g68q_spec_eq _ _ hh1 hh2 (Fintype.card C) (Fintype.card B) ?_⟩
  rw [Matrix.charpoly_transpose]
  exact Matrix.charpoly_mul_comm' X Xᴴ
