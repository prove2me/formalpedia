-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.pure_output_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T23:10:41.935614+00:00
-- url     : https://prove2.me/submissions/5d9b6258-00e6-449b-86a1-c3b017215ef2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48
open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem X7C11_spec {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) :
    (nonzeroSpectrum H).map (fun x : ℝ => (x : ℂ)) = H.charpoly.roots.filter (· ≠ 0) := by
  have h1 : (Finset.univ.val.map (QAlgorithms.ascEigenvalues H)) =
      Finset.univ.val.map hH.eigenvalues₀ := by
    have : QAlgorithms.ascEigenvalues H = hH.eigenvalues₀ ∘ Fin.revPerm := by
      funext k; simp [QAlgorithms.ascEigenvalues, hH]
    rw [this, ← Multiset.map_map, Multiset.map_univ_val_equiv]
  rw [nonzeroSpectrum, h1, hH.roots_charpoly_eq_eigenvalues₀, ← Multiset.map_map]
  conv_rhs => rw [Multiset.filter_map]
  congr 1
  refine Multiset.filter_congr (fun x _ => ?_)
  simp

theorem X7C11_roots {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι κ ℂ) :
    (M * Mᴴ).charpoly.roots.filter (· ≠ 0) = (Mᴴ * M).charpoly.roots.filter (· ≠ 0) := by
  have h := Matrix.charpoly_mul_comm' M Mᴴ
  have h2 := congrArg (fun p : Polynomial ℂ => p.roots.filter (· ≠ 0)) h
  rw [Polynomial.roots_mul, Polynomial.roots_mul, Polynomial.roots_X_pow, Polynomial.roots_X_pow,
    Multiset.filter_add, Multiset.filter_add] at h2
  · rw [Multiset.filter_nsmul, Multiset.filter_nsmul, Multiset.filter_singleton] at h2
    simpa using h2
  · exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero
  · exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero


theorem X7C11_recv {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (V : Matrix (B × C) A ℂ) (psi : EuclideanSpace ℂ A) :
    receiverChannel V (QAlgorithms.pureDensity psi) =
      (Matrix.of fun b c => ∑ a, V (b, c) a * psi a) *
        (Matrix.of fun b c => ∑ a, V (b, c) a * psi a)ᴴ := by
  ext b b'
  simp only [receiverChannel, QAlgorithms.traceRight, QAlgorithms.pureDensity, Matrix.of_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum, star_mul', Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun a' _ => ?_))
  simp only [RCLike.star_def]
  ring

theorem X7C11_compl {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (V : Matrix (B × C) A ℂ) (psi : EuclideanSpace ℂ A) :
    complementaryChannel V (QAlgorithms.pureDensity psi) =
      ((Matrix.of fun b c => ∑ a, V (b, c) a * psi a)ᴴ *
        (Matrix.of fun b c => ∑ a, V (b, c) a * psi a))ᵀ := by
  ext c c'
  simp only [complementaryChannel, QAlgorithms.traceLeft, QAlgorithms.pureDensity, Matrix.of_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, star_sum, star_mul',
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun a' _ => ?_))
  simp only [RCLike.star_def]
  ring


theorem X7C11_main {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C]
    (Phi : Superop A B) (PhiC : Superop A C)
    (hc : CPComplementary Phi PhiC) (psi : EuclideanSpace ℂ A) :
    nonzeroSpectrum (Phi (QAlgorithms.pureDensity psi)) =
      nonzeroSpectrum (PhiC (QAlgorithms.pureDensity psi)) := by
  obtain ⟨V, rfl, rfl⟩ := hc
  rw [X7C11_recv, X7C11_compl]
  set M : Matrix B C ℂ := Matrix.of fun b c => ∑ a, V (b, c) a * psi a
  have h1 : (M * Mᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self M
  have h2 : (Mᴴ * M)ᵀ.IsHermitian := (Matrix.isHermitian_conjTranspose_mul_self M).transpose
  apply Multiset.map_injective Complex.ofReal_injective
  rw [X7C11_spec _ h1, X7C11_spec _ h2, Matrix.charpoly_transpose, X7C11_roots]

end QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Claimed50.P48
open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)
open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)
open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)
open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P36 in
theorem solution {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (Phi : Superop A B) (PhiC : Superop A C) (hPhi : IsChannel Phi)
    (hc : CPComplementary Phi PhiC) (psi : EuclideanSpace ℂ A) (hpsi : IsState psi) :
    nonzeroSpectrum (Phi (pureDensity psi)) = nonzeroSpectrum (PhiC (pureDensity psi)) :=
  X7C11_main Phi PhiC hc psi
