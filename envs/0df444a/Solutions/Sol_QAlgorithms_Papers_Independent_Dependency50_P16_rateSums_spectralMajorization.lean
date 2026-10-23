-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P16.rateSums_spectralMajorization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:30:29.826395+00:00
-- url     : https://prove2.me/submissions/10edfadd-78d9-41e4-87fb-9a573cc5c5fb

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P16

open Matrix

lemma x8_spec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) *
        (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  rfl

lemma x8_perm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ∃ τ : Equiv.Perm (Fin n), ∀ i, hA.eigenvalues i = orderedSpectrum A hA (τ i) := by
  refine ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)).symm.trans (finCongr (Fintype.card_fin n)),
    fun i => ?_⟩
  simp only [IsHermitian.eigenvalues, orderedSpectrum, Equiv.trans_apply, finCongr_apply]
  rfl

lemma x8_diag {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℝ) (i : Fin n) :
    ((Q * diagonal (fun k => ((l k : ℝ) : ℂ)) * Qᴴ) i i).re =
      ∑ j, Complex.normSq (Q i j) * l j := by
  rw [mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_diagonal, conjTranspose_apply, Complex.star_def, mul_comm (Q i j), mul_assoc,
    Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]

lemma x8_rowsum {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    ∑ j, Complex.normSq (Q i j) = ((Q * Qᴴ) i i).re := by
  rw [mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [conjTranspose_apply, Complex.star_def, Complex.mul_conj]; rfl

lemma x8_colsum {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    ∑ i, Complex.normSq (Q i j) = ((Qᴴ * Q) j j).re := by
  rw [mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [conjTranspose_apply, Complex.star_def, mul_comm, Complex.mul_conj]; rfl

lemma x8_herm_sum {n r : ℕ} {M : Fin r → Matrix (Fin n) (Fin n) ℂ} (h : ∀ k, (M k).IsHermitian) :
    (∑ k, M k).IsHermitian := by
  rw [IsHermitian, conjTranspose_sum]
  exact Finset.sum_congr rfl (fun k _ => h k)

lemma x8_SH {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (V : Matrix (Fin n) (Fin n) ℂ) (hV1 : Vᴴ * V = 1) (hV2 : V * Vᴴ = 1) :
    majorizedBy (fun i => ((Vᴴ * A * V) i i).re) (orderedSpectrum A hA) := by
  set W : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  have hW1 : Wᴴ * W = 1 := Unitary.coe_star_mul_self _
  have hW2 : W * Wᴴ = 1 := Unitary.coe_mul_star_self _
  set Q := Vᴴ * W
  have hQ : Vᴴ * A * V = Q * diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) * Qᴴ := by
    conv_lhs => rw [x8_spec hA]
    simp only [Q, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rfl
  have hQQ : Q * Qᴴ = 1 := by
    simp only [Q, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W, hW2, Matrix.one_mul, hV1]
  have hQQ' : Qᴴ * Q = 1 := by
    simp only [Q, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V, hV2, Matrix.one_mul, hW1]
  set S : Matrix (Fin n) (Fin n) ℝ := fun i j => Complex.normSq (Q i j)
  have hS : S ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => Complex.normSq_nonneg _, fun i => ?_, fun j => ?_⟩
    · simp only [S]; rw [x8_rowsum, hQQ]; simp
    · simp only [S]; rw [x8_colsum, hQQ']; simp
  obtain ⟨w, hw0, hw1, hw⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  obtain ⟨τ, hτ⟩ := x8_perm hA
  have hx : (fun i => ((Vᴴ * A * V) i i).re) = S *ᵥ hA.eigenvalues := by
    funext i; rw [hQ, x8_diag]; rfl
  rw [hx, ← hw, Matrix.sum_mulVec]
  simp only [smul_mulVec, Matrix.permMatrix_mulVec]
  refine mem_convexHull_of_exists_fintype w (fun σ => hA.eigenvalues ∘ σ) hw0 hw1
    (fun σ => ⟨σ.trans τ, ?_⟩) rfl
  funext i; simp [hτ]

lemma x8_rates {n r : ℕ} (V : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) :
    (∀ i, ∑ j, rates V U i j = ((Uᴴ * (∑ k, V k * (V k)ᴴ) * U) i i).re) ∧
    (∀ i, ∑ j, rates V U j i = ((Uᴴ * (∑ k, (V k)ᴴ * V k) * U) i i).re) := by
  constructor
  · intro i
    simp only [rates]
    rw [Finset.sum_comm, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, Complex.re_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [x8_rowsum]
    congr 2
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hU2, Matrix.one_mul]
  · intro i
    simp only [rates]
    rw [Finset.sum_comm, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, Complex.re_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [x8_colsum]
    congr 2
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hU2, Matrix.one_mul]

lemma x8_main {n r : ℕ} (V : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (∀ i, ∑ j, rates V U i j = ((Uᴴ * (∑ k, V k * (V k)ᴴ) * U) i i).re) ∧
    (∀ i, ∑ j, rates V U j i = ((Uᴴ * (∑ k, (V k)ᴴ * V k) * U) i i).re) ∧
    (∀ i, (∑ j, rates V U i j) - (∑ j, rates V U j i) =
      ((Uᴴ * (∑ k, (V k * (V k)ᴴ - (V k)ᴴ * V k)) * U) i i).re) ∧
    (∀ i, (∑ j, rates V U i j) + (∑ j, rates V U j i) =
      ((Uᴴ * (∑ k, (V k * (V k)ᴴ + (V k)ᴴ * V k)) * U) i i).re) ∧
    spectrallyMajorizedBy (fun i => ∑ j, rates V U i j) (∑ k, V k * (V k)ᴴ) ∧
    spectrallyMajorizedBy (fun i => ∑ j, rates V U j i) (∑ k, (V k)ᴴ * V k) ∧
    spectrallyMajorizedBy (fun i => (∑ j, rates V U i j) - (∑ j, rates V U j i))
      (∑ k, (V k * (V k)ᴴ - (V k)ᴴ * V k)) ∧
    spectrallyMajorizedBy (fun i => (∑ j, rates V U i j) + (∑ j, rates V U j i))
      (∑ k, (V k * (V k)ᴴ + (V k)ᴴ * V k)) := by
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  obtain ⟨h1, h2⟩ := x8_rates V U hU1 hU2
  have h3 : ∀ i, (∑ j, rates V U i j) - (∑ j, rates V U j i) =
      ((Uᴴ * (∑ k, (V k * (V k)ᴴ - (V k)ᴴ * V k)) * U) i i).re := by
    intro i
    rw [h1, h2, Finset.sum_sub_distrib, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, Complex.sub_re]
  have h4 : ∀ i, (∑ j, rates V U i j) + (∑ j, rates V U j i) =
      ((Uᴴ * (∑ k, (V k * (V k)ᴴ + (V k)ᴴ * V k)) * U) i i).re := by
    intro i
    rw [h1, h2, Finset.sum_add_distrib, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Complex.add_re]
  have H1 : (∑ k, V k * (V k)ᴴ).IsHermitian :=
    x8_herm_sum (fun k => isHermitian_mul_conjTranspose_self (V k))
  have H2 : (∑ k, (V k)ᴴ * V k).IsHermitian :=
    x8_herm_sum (fun k => isHermitian_conjTranspose_mul_self (V k))
  have H3 : (∑ k, (V k * (V k)ᴴ - (V k)ᴴ * V k)).IsHermitian :=
    x8_herm_sum (fun k => (isHermitian_mul_conjTranspose_self (V k)).sub
      (isHermitian_conjTranspose_mul_self (V k)))
  have H4 : (∑ k, (V k * (V k)ᴴ + (V k)ᴴ * V k)).IsHermitian :=
    x8_herm_sum (fun k => (isHermitian_mul_conjTranspose_self (V k)).add
      (isHermitian_conjTranspose_mul_self (V k)))
  refine ⟨h1, h2, h3, h4, ⟨H1, ?_⟩, ⟨H2, ?_⟩, ⟨H3, ?_⟩, ⟨H4, ?_⟩⟩
  · rw [show (fun i => ∑ j, rates V U i j) = _ from funext h1]; exact x8_SH H1 U hU1 hU2
  · rw [show (fun i => ∑ j, rates V U j i) = _ from funext h2]; exact x8_SH H2 U hU1 hU2
  · rw [show (fun i => (∑ j, rates V U i j) - (∑ j, rates V U j i)) = _ from funext h3]
    exact x8_SH H3 U hU1 hU2
  · rw [show (fun i => (∑ j, rates V U i j) + (∑ j, rates V U j i)) = _ from funext h4]
    exact x8_SH H4 U hU1 hU2

end QAlgorithms.Papers.Independent.Dependency50.P16


open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing


local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

open QAlgorithms.Papers.Independent.Dependency50.P16 in
/-- arXiv:2308.00561v1, PDF p.29, Lemma B.2: Row and column sums of J and their majorization bounds. All four identities and all four majorizations are retained. Expectations use columns of U and real parts of Hermitian diagonal entries. U(n), not just SU(n), is quantified. -/
theorem solution {n r : ℕ} (hn : 2 ≤ n) (V : Fin r → Mat n)
    (U : Mat n) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (∀ i, ∑ j, rates V U i j = ((Uᴴ * (∑ k, V k * (V k)ᴴ) * U) i i).re) ∧
    (∀ i, ∑ j, rates V U j i = ((Uᴴ * (∑ k, (V k)ᴴ * V k) * U) i i).re) ∧
    (∀ i, (∑ j, rates V U i j) - (∑ j, rates V U j i) =
      ((Uᴴ * (∑ k, (V k * (V k)ᴴ - (V k)ᴴ * V k)) * U) i i).re) ∧
    (∀ i, (∑ j, rates V U i j) + (∑ j, rates V U j i) =
      ((Uᴴ * (∑ k, (V k * (V k)ᴴ + (V k)ᴴ * V k)) * U) i i).re) ∧
    spectrallyMajorizedBy (fun i => ∑ j, rates V U i j) (∑ k, V k * (V k)ᴴ) ∧
    spectrallyMajorizedBy (fun i => ∑ j, rates V U j i) (∑ k, (V k)ᴴ * V k) ∧
    spectrallyMajorizedBy (fun i => (∑ j, rates V U i j) - (∑ j, rates V U j i))
      (∑ k, (V k * (V k)ᴴ - (V k)ᴴ * V k)) ∧
    spectrallyMajorizedBy (fun i => (∑ j, rates V U i j) + (∑ j, rates V U j i))
      (∑ k, (V k * (V k)ᴴ + (V k)ᴴ * V k)) :=
  x8_main V U hU



