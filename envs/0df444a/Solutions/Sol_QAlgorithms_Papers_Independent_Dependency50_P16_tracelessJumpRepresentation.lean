-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P16.tracelessJumpRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:08:09.246136+00:00
-- url     : https://prove2.me/submissions/0b6b4a1d-7562-45c6-a3cc-938007d9c5ed

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P16

lemma x8_cp_apply {n r : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (V : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    cpGenerator K V X = (∑ k, V k * X * (V k)ᴴ) - K * X - X * Kᴴ := by
  simp [cpGenerator, sandwich, LinearMap.sum_apply, Matrix.mul_assoc]

lemma x8_block {n r : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (V : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (O P Q R A : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.IsHermitian) (hR : R.IsHermitian) :
    O * cpGenerator K V (P * A * R) * Q =
      (∑ k, (O * V k * P) * A * (Q * V k * R)ᴴ) -
        (O * K * P) * A * (R * Q) - (O * P) * A * (Q * K * R)ᴴ := by
  rw [x8_cp_apply]
  simp only [Matrix.conjTranspose_mul, hQ.eq, hR.eq, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

lemma x8_gauge {n r : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (V : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (c : Fin r → ℂ) (z : ℂ) (hz : z + conj z = ∑ k, ((Complex.normSq (c k) : ℝ) : ℂ)) :
    cpGenerator (K + ∑ k, conj (c k) • V k + z • (1 : Matrix (Fin n) (Fin n) ℂ))
      (fun k => V k + c k • (1 : Matrix (Fin n) (Fin n) ℂ)) = cpGenerator K V := by
  apply LinearMap.ext; intro X
  rw [x8_cp_apply, x8_cp_apply]
  simp only [Finset.sum_add_distrib, Matrix.conjTranspose_add, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.add_mul, Matrix.mul_add,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.one_mul, Complex.star_def, Complex.conj_conj, smul_add, smul_smul]
  simp only [← Complex.normSq_eq_conj_mul_self, ← Finset.sum_smul]
  rw [← hz, add_smul]
  abel

lemma x8_traceless {n r : ℕ} (hn : 2 ≤ n) (K : Matrix (Fin n) (Fin n) ℂ)
    (V : Fin r → Matrix (Fin n) (Fin n) ℂ) :
    ∃ (Knew : Matrix (Fin n) (Fin n) ℂ) (W : Fin r → Matrix (Fin n) (Fin n) ℂ),
      cpGenerator Knew W = cpGenerator K V ∧ ∀ k, (W k).trace = 0 := by
  set c : Fin r → ℂ := fun k => -((V k).trace / (n : ℂ))
  refine ⟨K + ∑ k, conj (c k) • V k +
    (((1 / 2 : ℝ) * ∑ k, Complex.normSq (c k) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ),
    fun k => V k + c k • (1 : Matrix (Fin n) (Fin n) ℂ), x8_gauge K V c _ ?_, fun k => ?_⟩
  · rw [Complex.conj_ofReal, ← Complex.ofReal_add, ← Complex.ofReal_sum]
    congr 1; ring
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, c,
      smul_eq_mul]
    field_simp; ring

lemma x8_shift {n : ℕ} (D : LindbladData n) (c : Fin D.count → ℂ) (a : ℝ) :
    (shiftedDriftHamiltonian D c a).IsHermitian ∧
      cpGenerator (Complex.I • shiftedDriftHamiltonian D c a + (1 / 2 : ℂ) •
        ∑ k, (gaugeJumps D c k)ᴴ * gaugeJumps D c k) (gaugeJumps D c) = gkslGenerator D := by
  have hI : (1 / (2 * Complex.I)) = -(Complex.I / 2) := by
    field_simp; rw [Complex.I_sq]; ring
  constructor
  · unfold shiftedDriftHamiltonian
    refine (D.drift_hermitian.add ?_).add ?_
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose,
        Complex.star_def, Complex.conj_conj, hI, map_neg, map_div₀, Complex.conj_I, Complex.conj_ofNat]
      rw [show ∑ x, (c x • (D.jump x)ᴴ - (starRingEnd ℂ) (c x) • D.jump x) =
          -∑ x, ((starRingEnd ℂ) (c x) • D.jump x - c x • (D.jump x)ᴴ) by
            rw [← Finset.sum_neg_distrib]; simp, smul_neg, ← neg_smul]
      congr 1; ring
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
      simp [Complex.conj_ofReal]
  · have key : Complex.I • shiftedDriftHamiltonian D c a + (1 / 2 : ℂ) •
        ∑ k, (gaugeJumps D c k)ᴴ * gaugeJumps D c k =
        driftK D + ∑ k, conj (c k) • D.jump k +
          ((((1 / 2 : ℝ) * ∑ k, Complex.normSq (c k) : ℝ) : ℂ) + Complex.I * a) •
            (1 : Matrix (Fin n) (Fin n) ℂ) := by
      unfold shiftedDriftHamiltonian gaugeJumps driftK
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
        Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.one_mul, Finset.sum_add_distrib, smul_add, smul_sub, Finset.smul_sum, smul_smul,
        Complex.star_def, Finset.sum_sub_distrib, add_smul, Complex.ofReal_mul, Complex.ofReal_sum,
        Finset.mul_sum, Finset.sum_smul, Complex.normSq_eq_conj_mul_self, hI]
      have h1 : ∀ x : ℂ, Complex.I * -(Complex.I / 2) * x = 1 / 2 * x := by
        intro x; field_simp; rw [Complex.I_sq]; ring
      have h2 : ∀ x : ℂ, Complex.I * (-(Complex.I / 2) * x) = 1 / 2 * x := by
        intro x; rw [← mul_assoc, h1]
      simp only [h2, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
      have hs : ∑ x, (starRingEnd ℂ) (c x) • D.jump x =
          ∑ x, (1 / 2 * (starRingEnd ℂ) (c x)) • D.jump x +
            ∑ x, (1 / 2 * (starRingEnd ℂ) (c x)) • D.jump x := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [← add_smul]; congr 1; ring
      have hc : ∀ i, c i * (starRingEnd ℂ) (c i) = (starRingEnd ℂ) (c i) * c i :=
        fun i => mul_comm _ _
      simp only [hc, hs]
      abel
    rw [key]
    unfold gkslGenerator gaugeJumps
    refine x8_gauge _ _ c _ ?_
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
      ← Complex.ofReal_sum]
    push_cast; ring

lemma x8_pg {n r : ℕ} (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) (hij : i ≠ j) :
    -(populationGenerator V U i j) = -(∑ k, Complex.normSq ((Uᴴ * V k * U) i j)) := by
  simp [populationGenerator, rates, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij]

lemma x8_zeros {n r : ℕ} (V : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) (hij : i ≠ j) :
    (∀ (m : ℕ), 0 < m → ∀ (a : Fin m → ℝ) (U : Fin m → Matrix (Fin n) (Fin n) ℂ),
      (∀ k, 0 < a k) → (∑ k, a k) = 1 → (∀ k, specialUnitary (U k)) →
      (∑ k, a k * (-(populationGenerator V (U k) i j))) = 0 →
      ∀ k, -(populationGenerator V (U k) i j) = 0) ∧
    (∀ U : Matrix (Fin n) (Fin n) ℂ, specialUnitary U → -(populationGenerator V U i j) = 0 →
      ∀ k, (Uᴴ * V k * U) i j = 0) := by
  have hnn : ∀ U : Matrix (Fin n) (Fin n) ℂ, 0 ≤ ∑ k, Complex.normSq ((Uᴴ * V k * U) i j) :=
    fun U => Finset.sum_nonneg (fun k _ => Complex.normSq_nonneg _)
  constructor
  · intro m _ a U ha _ _ hsum k
    simp only [x8_pg V _ i j hij] at hsum ⊢
    have h0 : ∀ l ∈ Finset.univ, 0 ≤ a l * (∑ k, Complex.normSq (((U l)ᴴ * V k * U l) i j)) :=
      fun l _ => mul_nonneg (ha l).le (hnn (U l))
    have hs : ∑ l, a l * (∑ k, Complex.normSq (((U l)ᴴ * V k * U l) i j)) = 0 := by
      have : ∑ l, a l * -(∑ k, Complex.normSq (((U l)ᴴ * V k * U l) i j)) =
          -∑ l, a l * (∑ k, Complex.normSq (((U l)ᴴ * V k * U l) i j)) := by
        rw [← Finset.sum_neg_distrib]; simp
      linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg h0).1 hs k (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (ha k).ne'
    · rw [h, neg_zero]
  · intro U _ h k
    rw [x8_pg V _ i j hij, neg_eq_zero] at h
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => Complex.normSq_nonneg ((Uᴴ * V k * U) i j))).1 h k (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this

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
/-- arXiv:2308.00561v1, PDF p.31, Unnumbered traceless jump representation. This uses only scalar-shift freedom, not the false unrestricted coisometry transformation. r=0 is allowed. -/
theorem solution {n r : ℕ} (hn : 2 ≤ n) (K : Mat n) (V : Fin r → Mat n) :
    ∃ (Knew : Mat n) (W : Fin r → Mat n),
      cpGenerator Knew W = cpGenerator K V ∧ ∀ k, (W k).trace = 0 :=
  x8_traceless hn K V



