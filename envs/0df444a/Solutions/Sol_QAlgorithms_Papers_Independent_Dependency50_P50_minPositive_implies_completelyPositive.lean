-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P50.minPositive_implies_completelyPositive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:20:19.363767+00:00
-- url     : https://prove2.me/submissions/2c3c8c7c-c1d9-491d-a5c3-44d9a2bdf2c4

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace X6P50MP

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


lemma posSemidef_of_forall {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (h : ∀ v : ι → ℂ, 0 ≤ star v ⬝ᵥ (M *ᵥ v)) : M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ h
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  have hz := h v.ofLp
  have hre : (star v.ofLp ⬝ᵥ (M *ᵥ v.ofLp)).im = 0 := (Complex.nonneg_iff.mp hz).2.symm
  have hin : inner ℂ (M.toEuclideanLin v) v = conj (star v.ofLp ⬝ᵥ (M *ᵥ v.ofLp)) := by
    rw [← inner_conj_symm, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply,
      dotProduct_comm]
  rw [hin, Complex.conj_conj]
  apply Complex.ext <;> simp [hre]

lemma cp_of_j2 {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hJ : (j2 T).PosSemidef) : QAlgorithms.Entanglement.IsCompletelyPositive T := by
  intro r X hX
  obtain ⟨B, hB⟩ := psd_decomp X hX
  have hB' : X = ∑ k, Matrix.vecMulVec (star (B k)) (star (star (B k))) := by
    simpa using hB
  rw [hB', idTensor_sum]
  refine Matrix.posSemidef_sum _ fun k _ => ?_
  rw [idTensor_rankOne]
  exact hJ.mul_mul_conjTranspose_same _

/-- every coefficient matrix factors through `Fin (min n m)` -/
lemma factor {n m : ℕ} (u : Fin n × Fin m → ℂ) :
    ∃ (X : Matrix (Fin n) (Fin (min n m)) ℂ) (Y : Matrix (Fin m) (Fin (min n m)) ℂ),
      ∀ i j, u (i, j) = ∑ s, X i s * Y j s := by
  rcases le_total n m with h | h
  · let e : Fin (min n m) ≃ Fin n := finCongr (min_eq_left h)
    refine ⟨fun i s => if i = e s then 1 else 0, fun j s => u (e s, j), fun i j => ?_⟩
    rw [← e.symm.sum_comp]
    simp
  · let e : Fin (min n m) ≃ Fin m := finCongr (min_eq_right h)
    refine ⟨fun i s => u (i, e s), fun j s => if j = e s then 1 else 0, fun i j => ?_⟩
    rw [← e.symm.sum_comp]
    simp

lemma quad_nonneg {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ A : Matrix (Fin (min n m) × Fin n) (Fin (min n m) × Fin n) ℂ,
      A.PosSemidef → (QAlgorithms.idTensorSuperop (R := Fin (min n m)) T A).PosSemidef)
    (u : Fin n × Fin m → ℂ) : 0 ≤ star u ⬝ᵥ (j2 T *ᵥ u) := by
  obtain ⟨X, Y, hXY⟩ := factor u
  let w : Fin (min n m) × Fin n → ℂ := fun p => conj (X p.2 p.1)
  let z : Fin (min n m) × Fin m → ℂ := fun p => Y p.2 p.1
  have hP := h _ (Matrix.posSemidef_vecMulVec_self_star w)
  rw [idTensor_rankOne] at hP
  have hu : u = (K (m := m) w)ᴴ *ᵥ z := by
    funext p
    obtain ⟨i, j⟩ := p
    rw [hXY]
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, K, Matrix.of_apply,
      Fintype.sum_prod_type, w, z, star_mul', RCLike.star_def, Complex.conj_conj]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb, Ne.symm hb]
    · simp
  have := hP.dotProduct_mulVec_nonneg z
  rw [hu, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec]
  rwa [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at this

end X6P50MP

open QAlgorithms.Papers.Independent.Dependency50.P50 X6P50MP in
theorem solution {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) :
    (∀ A : Matrix (Fin (min n m) × Fin n) (Fin (min n m) × Fin n) ℂ,
      A.PosSemidef →
        (QAlgorithms.idTensorSuperop (R := Fin (min n m)) T A).PosSemidef) → QAlgorithms.Entanglement.IsCompletelyPositive T := by
  intro h
  exact cp_of_j2 T (posSemidef_of_forall _ (quad_nonneg T h))
