-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P40.noiseRecoveryChoi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:49:05.464438+00:00
-- url     : https://prove2.me/submissions/34cff4a4-1028-4b9c-a6a3-4c701b662a9c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

lemma g52a_single_conj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (a b : Fin n) (o p : Fin m) :
    (A * Matrix.single a b (1 : ℂ) * Aᴴ) o p = A o a * star (A p b) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [Matrix.conjTranspose_apply]
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [Matrix.single_apply, hc, Ne.symm hc]
    · simp
  · intro c _ hc
    have : (A * Matrix.single a b (1 : ℂ)) o c = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      simp [Matrix.single_apply, hc, Ne.symm hc]
    rw [this, zero_mul]
  · simp

lemma g52a_kraus_comp {h k m n : ℕ} (E : Fin m → Matrix (Fin k) (Fin h) ℂ)
    (R : Fin n → Matrix (Fin h) (Fin k) ℂ) (X : Matrix (Fin h) (Fin h) ℂ) :
    krausApply R (krausApply E X) = ∑ i, ∑ j, (R i * E j) * X * (R i * E j)ᴴ := by
  simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

lemma g52a_L1 {h k : ℕ} (M : Matrix (Fin k) (Fin h) ℂ)
    (X : Matrix (Fin h × Fin k) (Fin h × Fin k) ℂ) (o a : Fin h) (q : Fin h × Fin k) :
    (Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) Mᵀ * X) (o, a) q =
      ∑ y, M y a * X (o, y) q := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single o]
  · simp [Matrix.kronecker, Matrix.one_apply]
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [Matrix.kronecker, Matrix.one_apply, Ne.symm hx]
  · simp

lemma g52a_L2 {h k : ℕ} (M : Matrix (Fin k) (Fin h) ℂ)
    (Y : Matrix (Fin h × Fin h) (Fin h × Fin k) ℂ) (q : Fin h × Fin h) (p b : Fin h) :
    (Y * Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) (M.map (fun z => conj z))) q (p, b) =
      ∑ y, Y q (p, y) * conj (M y b) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single p]
  · simp [Matrix.kronecker, Matrix.one_apply]
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [Matrix.kronecker, Matrix.one_apply, hx]
  · simp

/-- PDF pp.3–4, (18)–(19): Choi composition for noise followed by recovery. -/
theorem solution {h k m n : ℕ} (hh : 0 < h) (hk : 0 < k)
    (E : Fin m → Matrix (Fin k) (Fin h) ℂ) (hE : IsKrausFamily E)
    (R : Fin n → Matrix (Fin h) (Fin k) ℂ) (hR : IsKrausFamily R) :
    outputFirstChoi (krausApply R ∘ krausApply E) =
      ∑ i, ∑ j, dyad (operatorKet (R i * E j)) (operatorKet (R i * E j)) ∧
    outputFirstChoi (krausApply R ∘ krausApply E) =
      ∑ j, Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) (E j)ᵀ * krausChoi R *
        Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) ((E j).map (fun z => conj z)) := by
  have h1 : outputFirstChoi (krausApply R ∘ krausApply E) =
      ∑ i, ∑ j, dyad (operatorKet (R i * E j)) (operatorKet (R i * E j)) := by
    ext ⟨o, a⟩ ⟨p, b⟩
    show (krausApply R (krausApply E (Matrix.single a b 1))) o p = _
    rw [g52a_kraus_comp]
    simp only [Matrix.sum_apply, g52a_single_conj, dyad, operatorKet, PiLp.toLp_apply,
      RCLike.star_def]
  refine ⟨h1, ?_⟩
  rw [h1]
  ext ⟨o, a⟩ ⟨p, b⟩
  simp only [Matrix.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [g52a_L2]
  simp only [g52a_L1]
  simp only [krausChoi, Matrix.sum_apply, dyad, operatorKet, PiLp.toLp_apply,
    Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, i0]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, i0]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun t _ => ?_
  ring


end

