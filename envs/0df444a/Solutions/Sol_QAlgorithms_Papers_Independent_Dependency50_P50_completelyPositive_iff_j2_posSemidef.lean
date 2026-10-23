-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P50.completelyPositive_iff_j2_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:16:52.510616+00:00
-- url     : https://prove2.me/submissions/032194bd-e379-4b85-a5f6-dee9dfcd99c7

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace X6P50CP

open QAlgorithms.Papers.Independent.Dependency50.P50

lemma j2_apply {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (p q : Fin n × Fin m) : j2 T p q = T (Matrix.single p.1 q.1 1) p.2 q.2 := rfl

lemma expand {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin m) :
    T A a b = ∑ i, ∑ j, A i j * T (Matrix.single i j 1) a b := by
  have hA : A = ∑ i : Fin n, ∑ j : Fin n, A i j • Matrix.single i j (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    simp [Matrix.smul_single]
  conv_lhs => rw [hA]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

lemma psd_decomp {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, A = ∑ k, Matrix.vecMulVec (star (B k)) (B k) := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  open scoped MatrixOrder in
  have hB : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  open scoped MatrixOrder in
  have hAB : A = (CFC.sqrt A)ᴴ * CFC.sqrt A := by
    rw [hB.isHermitian.eq, CFC.sqrt_mul_sqrt_self A h0]
  refine ⟨CFC.sqrt A, ?_⟩
  conv_lhs => rw [hAB]
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.sum_apply, Matrix.conjTranspose_apply]

lemma idTensor_sum {r n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    {κ : Type*} (s : Finset κ) (X : κ → Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) :
    QAlgorithms.idTensorSuperop (R := Fin r) T (∑ k ∈ s, X k) =
      ∑ k ∈ s, QAlgorithms.idTensorSuperop (R := Fin r) T (X k) := by
  ext p q
  simp only [QAlgorithms.idTensorSuperop, Matrix.of_apply, Matrix.sum_apply]
  have : (Matrix.of fun i i' => ∑ k ∈ s, X k (p.1, i) (q.1, i')) =
      ∑ k ∈ s, Matrix.of fun i i' => X k (p.1, i) (q.1, i') := by
    ext i i'; simp [Matrix.sum_apply]
  rw [this, map_sum, Matrix.sum_apply]

/-- the congruence factor -/
def K {r n m : ℕ} (v : Fin r × Fin n → ℂ) : Matrix (Fin r × Fin m) (Fin n × Fin m) ℂ :=
  Matrix.of fun p q => v (p.1, q.1) * (if p.2 = q.2 then 1 else 0)

lemma idTensor_rankOne {r n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (v : Fin r × Fin n → ℂ) :
    QAlgorithms.idTensorSuperop (R := Fin r) T (Matrix.vecMulVec v (star v)) =
      K (m := m) v * j2 T * (K (m := m) v)ᴴ := by
  ext p q
  obtain ⟨a, i⟩ := p
  obtain ⟨b, j⟩ := q
  show T _ i j = _
  rw [expand T]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, K, j2_apply, Fintype.sum_prod_type,
    Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [apply_ite star, star_zero, mul_ite, mul_zero]
  conv_rhs => arg 2; ext x; rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [mul_one, star_mul']
  ring

end X6P50CP

open QAlgorithms.Papers.Independent.Dependency50.P50 X6P50CP in
theorem solution {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) :
    QAlgorithms.Entanglement.IsCompletelyPositive T ↔ (j2 T).PosSemidef := by
  constructor
  · intro hT
    let w : Fin n × Fin n → ℂ := fun p => if p.1 = p.2 then 1 else 0
    have hw : (Matrix.vecMulVec w (star w)).PosSemidef := Matrix.posSemidef_vecMulVec_self_star w
    have := hT n _ hw
    convert this using 1
    ext p q
    obtain ⟨a, i⟩ := p
    obtain ⟨b, j⟩ := q
    have hblk : (Matrix.of fun x y => Matrix.vecMulVec w (star w) (a, x) (b, y)) =
        Matrix.single a b (1 : ℂ) := by
      ext x y
      simp only [w, Matrix.of_apply, Matrix.vecMulVec_apply, Matrix.single_apply, Pi.star_apply]
      split_ifs <;> simp_all
    show T (Matrix.single a b 1) i j = T (Matrix.of fun x y => Matrix.vecMulVec w (star w) (a, x) (b, y)) i j
    rw [hblk]
  · intro hJ r X hX
    obtain ⟨B, hB⟩ := psd_decomp X hX
    have hB' : X = ∑ k, Matrix.vecMulVec (star (B k)) (star (star (B k))) := by
      simpa using hB
    rw [hB', idTensor_sum]
    refine Matrix.posSemidef_sum _ fun k _ => ?_
    rw [idTensor_rankOne]
    exact hJ.mul_mul_conjTranspose_same _
