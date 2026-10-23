-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P50.kPositive_iff_schmidt_blockPositive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:22:36.885291+00:00
-- url     : https://prove2.me/submissions/92b11c1f-44bd-4390-a14f-0517c779bdce

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace X6P50K3

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


lemma factor_of_rank_le {n m k : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (h : A.rank ≤ k) :
    ∃ (X : Matrix (Fin n) (Fin k) ℂ) (Y : Matrix (Fin m) (Fin k) ℂ),
      ∀ i j, A i j = ∑ s, X i s * Y j s := by
  set S := Submodule.span ℂ (Set.range A.col) with hS
  set r := Module.finrank ℂ S with hr
  have hrk : r ≤ k := by rw [hr, ← Matrix.rank_eq_finrank_span_cols]; exact h
  let b := Module.finBasis ℂ S
  have hmem : ∀ j, A.col j ∈ S := fun j => Submodule.subset_span ⟨j, rfl⟩
  let c : Fin m → Fin r → ℂ := fun j t => b.repr ⟨A.col j, hmem j⟩ t
  refine ⟨fun i s => if hs : s.val < r then (b ⟨s.val, hs⟩ : Fin n → ℂ) i else 0,
    fun j s => if hs : s.val < r then c j ⟨s.val, hs⟩ else 0, fun i j => ?_⟩
  have hcol : A.col j = ∑ t, c j t • (b t : Fin n → ℂ) := by
    have := b.sum_repr ⟨A.col j, hmem j⟩
    have h2 := congrArg Subtype.val this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  have hA : A i j = ∑ t, (b t : Fin n → ℂ) i * c j t := by
    have := congrFun hcol i
    simp only [Matrix.col, Matrix.transpose_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at this
    rw [this]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  rw [hA]
  let g : ℕ → ℂ := fun x => if hx : x < r then (b ⟨x, hx⟩ : Fin n → ℂ) i * c j ⟨x, hx⟩ else 0
  have h1 : ∑ t : Fin r, (b t : Fin n → ℂ) i * c j t = ∑ x ∈ Finset.range r, g x := by
    rw [← Fin.sum_univ_eq_sum_range g r]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [g, t.isLt]
  have h2 : ∑ s : Fin k, (if hs : s.val < r then (b ⟨s.val, hs⟩ : Fin n → ℂ) i else 0) *
      (if hs : s.val < r then c j ⟨s.val, hs⟩ else 0) = ∑ x ∈ Finset.range k, g x := by
    rw [← Fin.sum_univ_eq_sum_range g k]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [g]
    split_ifs <;> simp
  rw [h1, h2]
  refine Finset.sum_subset (Finset.range_subset_range.mpr hrk) fun x _ hx => ?_
  simp only [Finset.mem_range, not_lt] at hx
  simp [g, not_lt.mpr hx]

lemma quad_nonneg_k {n m k : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ A : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ,
      A.PosSemidef → (QAlgorithms.idTensorSuperop (R := Fin k) T A).PosSemidef)
    (u : Fin n × Fin m → ℂ) (X : Matrix (Fin n) (Fin k) ℂ) (Y : Matrix (Fin m) (Fin k) ℂ)
    (hXY : ∀ i j, u (i, j) = ∑ s, X i s * Y j s) : 0 ≤ star u ⬝ᵥ (j2 T *ᵥ u) := by
  let w : Fin k × Fin n → ℂ := fun p => conj (X p.2 p.1)
  let z : Fin k × Fin m → ℂ := fun p => Y p.2 p.1
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
    · intro b _ hb; simp [hb]
    · simp
  have := hP.dotProduct_mulVec_nonneg z
  rw [hu, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec]
  rwa [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at this

lemma inner_eq {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    inner ℂ v (QAlgorithms.act M v) = star v.ofLp ⬝ᵥ (M *ᵥ v.ofLp) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

end X6P50K3

open QAlgorithms.Papers.Independent.Dependency50.P50 X6P50K3 in
theorem solution {n m k : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hk : 0 < k) (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) :
    (∀ A : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ,
      A.PosSemidef → (QAlgorithms.idTensorSuperop (R := Fin k) T A).PosSemidef) ↔ ∀ v : Bipartite n m, schmidtNumber v ≤ k →
      0 ≤ inner ℂ v (QAlgorithms.act (j2 T) v) := by
  constructor
  · intro h v hv
    obtain ⟨X, Y, hXY⟩ := factor_of_rank_le _ hv
    rw [inner_eq]
    exact quad_nonneg_k T h v.ofLp X Y fun i j => hXY i j
  · intro h A hA
    obtain ⟨B, hB⟩ := psd_decomp A hA
    have hB' : A = ∑ l, Matrix.vecMulVec (star (B l)) (star (star (B l))) := by
      simpa using hB
    rw [hB', idTensor_sum]
    refine posSemidef_of_forall _ fun z => ?_
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_nonneg fun l _ => ?_
    rw [idTensor_rankOne, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec]
    set u := (K (m := m) (star (B l)))ᴴ *ᵥ z with hu
    have hsu : star z ᵥ* K (m := m) (star (B l)) = star u := by
      rw [hu, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    rw [hsu]
    have hsn : schmidtNumber (WithLp.toLp 2 u : Bipartite n m) ≤ k := by
      unfold schmidtNumber
      have hfac : (Matrix.of fun (i : Fin n) (j : Fin m) => (WithLp.toLp 2 u : Bipartite n m) (i, j)) =
          (Matrix.of fun (i : Fin n) (s : Fin k) => star (star (B l) (s, i))) *
            (Matrix.of fun (s : Fin k) (j : Fin m) => z (s, j)) := by
        ext i j
        simp only [hu, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, K, Matrix.of_apply,
          Fintype.sum_prod_type, Matrix.mul_apply, PiLp.toLp_apply]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb; simp [hb]
        · simp
      rw [hfac]
      refine le_trans (Matrix.rank_mul_le_left _ _) ?_
      simpa using Matrix.rank_le_card_width
        (Matrix.of fun (i : Fin n) (s : Fin k) => star (star (B l) (s, i)))
    have := h _ hsn
    rw [inner_eq] at this
    exact this
