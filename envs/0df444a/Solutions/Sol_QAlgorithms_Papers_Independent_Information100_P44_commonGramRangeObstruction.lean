-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.commonGramRangeObstruction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:39:53.878712+00:00
-- url     : https://prove2.me/submissions/baf3a6f2-b19b-496e-9311-e3003ec39252

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

lemma X7_LI_cols {a b : Type*} [Fintype a] [Fintype b] (N : Matrix a b ℂ) (k : ℕ)
    (hk : k ≤ N.rank) : ∃ cols : Fin k ↪ b, LinearIndependent ℂ (fun j => N.col (cols j)) := by
  obtain ⟨κ, f, hf, hsp, hli⟩ := exists_linearIndependent' ℂ N.col
  haveI : Fintype κ := Fintype.ofInjective f hf
  have hcard : N.rank = Fintype.card κ := by
    rw [Matrix.rank_eq_finrank_span_cols, ← hsp, finrank_span_eq_card hli]
  have hk' : k ≤ Fintype.card κ := hcard ▸ hk
  let e : Fin k ↪ κ := (Fin.castLEEmb hk').trans (Fintype.equivFin κ).symm.toEmbedding
  refine ⟨e.trans ⟨f, hf⟩, ?_⟩
  exact hli.comp e e.injective

lemma X7_rank_minors {a b : Type*} [Fintype a] [Fintype b] (M : Matrix a b ℂ) (r : ℕ) :
    M.rank ≤ r ↔ AllMinorsZero (r+1) M := by
  constructor
  · intro h rows cols
    by_contra hdet
    have hu : IsUnit (M.submatrix rows cols) := (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hdet)
    have h1 := Matrix.rank_of_isUnit _ hu
    have h2 := Matrix.rank_submatrix_le M rows cols
    simp only [Fintype.card_fin] at h1
    omega
  · intro h
    by_contra hlt
    push_neg at hlt
    obtain ⟨cols, hcols⟩ := X7_LI_cols M (r+1) hlt
    set N := M.submatrix id cols with hN
    have hNr : N.rank = r + 1 := by
      rw [Matrix.rank_eq_finrank_span_cols]
      have : N.col = fun j => M.col (cols j) := by ext j i; rfl
      rw [this, finrank_span_eq_card hcols, Fintype.card_fin]
    have hNt : r + 1 ≤ Nᵀ.rank := by rw [Matrix.rank_transpose, hNr]
    obtain ⟨rows, hrows⟩ := X7_LI_cols Nᵀ (r+1) hNt
    have hli : LinearIndependent ℂ (M.submatrix rows cols).row := by
      have : (M.submatrix rows cols).row = fun j => Nᵀ.col (rows j) := by ext j i; rfl
      rw [this]; exact hrows
    have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hli
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero (h rows cols)

lemma X7_range_eq {a b : Type*} [Fintype b] (M : Matrix a b ℂ) :
    Set.range M.mulVec = (LinearMap.range M.mulVecLin : Set (a → ℂ)) := by
  ext x; simp

lemma X7_range_augment {a b c : Type*} [Fintype b] [Fintype c] (A : Matrix a b ℂ) (B : Matrix a c ℂ) :
    LinearMap.range (augment A B).mulVecLin =
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
  have key : ∀ v : b ⊕ c → ℂ, (augment A B) *ᵥ v = A *ᵥ (v ∘ Sum.inl) + B *ᵥ (v ∘ Sum.inr) := by
    intro v; ext i
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, augment]
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, key]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  · apply sup_le
    · rintro _ ⟨x, rfl⟩
      refine ⟨Sum.elim x 0, ?_⟩
      rw [Matrix.mulVecLin_apply, key, Matrix.mulVecLin_apply]
      have : (Sum.elim x 0 : b ⊕ c → ℂ) ∘ Sum.inr = 0 := by ext; simp
      rw [this, Matrix.mulVec_zero, add_zero]; rfl
    · rintro _ ⟨y, rfl⟩
      refine ⟨Sum.elim 0 y, ?_⟩
      rw [Matrix.mulVecLin_apply, key, Matrix.mulVecLin_apply]
      have : (Sum.elim 0 y : b ⊕ c → ℂ) ∘ Sum.inl = 0 := by ext; simp
      rw [this, Matrix.mulVec_zero, zero_add]; rfl

lemma X7_range_mul_le {a b c : Type*} [Fintype b] [Fintype c] (X : Matrix a b ℂ) (Y : Matrix b c ℂ) :
    LinearMap.range (X * Y).mulVecLin ≤ LinearMap.range X.mulVecLin := by
  rintro _ ⟨v, rfl⟩
  exact ⟨Y *ᵥ v, by simp [Matrix.mulVec_mulVec]⟩

lemma X7_range_gram {a b : Type*} [Fintype a] [Fintype b] (R : Matrix a b ℂ) :
    LinearMap.range (Rᴴ * R).mulVecLin = LinearMap.range Rᴴ.mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_le (X7_range_mul_le _ _)
  have h1 : (Rᴴ * R).rank = Rᴴ.rank := by
    rw [Matrix.rank_conjTranspose_mul_self, Matrix.rank_conjTranspose]
  exact h1.symm.le

lemma X7_subset_iff_rank {d b : Type*} [Fintype d] [Fintype b] (A : Matrix d d ℂ) (B : Matrix d b ℂ) :
    LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin ↔ (augment A B).rank ≤ A.rank := by
  rw [Matrix.rank, Matrix.rank, X7_range_augment]
  constructor
  · intro h; rw [sup_eq_left.mpr h]
  · intro h
    have := Submodule.eq_of_le_of_finrank_le (le_sup_left : LinearMap.range A.mulVecLin ≤ _) h
    calc LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin :=
          le_sup_right
      _ = LinearMap.range A.mulVecLin := this.symm

lemma X7_cg_main {d m : ℕ} (n : Fin m → ℕ) (A : Mat d)
    (B : (a : Fin m) → Matrix (Fin d) (Fin (n a)) ℂ)
    (C : (a b : Fin m) → Matrix (Fin (n a)) (Fin (n b)) ℂ)
    (r : ℕ) (hrank : A.rank = r)
    (hpos : (commonGram n A B C).PosSemidef) :
    ∀ a,
      Set.range (B a).mulVec ⊆ Set.range A.mulVec ∧
      (augment A (B a)).rank ≤ r ∧ AllMinorsZero (r+1) (augment A (B a)) ∧
      ((Set.range (B a).mulVec ⊆ Set.range A.mulVec) ↔ (augment A (B a)).rank ≤ r) ∧
      ((augment A (B a)).rank ≤ r ↔ AllMinorsZero (r+1) (augment A (B a))) := by
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos.nonneg
  set R1 := R.submatrix id Sum.inl with hR1
  have hA' : A = R1ᴴ * R1 := by
    ext i j
    rw [show A i j = commonGram n A B C (Sum.inl i) (Sum.inl j) from rfl, hR]
    simp [Matrix.mul_apply, R1, Matrix.star_apply]
  intro a
  have hB' : B a = R1ᴴ * R.submatrix id (fun k => Sum.inr ⟨a, k⟩) := by
    ext i k
    rw [show B a i k = commonGram n A B C (Sum.inl i) (Sum.inr ⟨a, k⟩) from rfl, hR]
    simp [Matrix.mul_apply, R1, Matrix.star_apply]
  have hsub : LinearMap.range (B a).mulVecLin ≤ LinearMap.range A.mulVecLin := by
    rw [hA', X7_range_gram, hB']; exact X7_range_mul_le _ _
  have hiff1 : (Set.range (B a).mulVec ⊆ Set.range A.mulVec) ↔ (augment A (B a)).rank ≤ r := by
    rw [X7_range_eq, X7_range_eq, SetLike.coe_subset_coe, X7_subset_iff_rank, hrank]
  have hiff2 := X7_rank_minors (augment A (B a)) r
  have h1 : Set.range (B a).mulVec ⊆ Set.range A.mulVec := by
    rw [X7_range_eq, X7_range_eq, SetLike.coe_subset_coe]; exact hsub
  exact ⟨h1, hiff1.mp h1, hiff2.mp (hiff1.mp h1), hiff1, hiff2⟩

end

end QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P44 in
theorem solution {d m : ℕ} (n : Fin m → ℕ) (A : Mat d)
    (B : (a : Fin m) → Matrix (Fin d) (Fin (n a)) ℂ)
    (C : (a b : Fin m) → Matrix (Fin (n a)) (Fin (n b)) ℂ)
    (r : ℕ) (hA : A.PosSemidef) (hrank : A.rank = r) (hr : r < d)
    (hpos : (commonGram n A B C).PosSemidef) :
    ∀ a,
      Set.range (B a).mulVec ⊆ Set.range A.mulVec ∧
      (augment A (B a)).rank ≤ r ∧ AllMinorsZero (r+1) (augment A (B a)) ∧
      ((Set.range (B a).mulVec ⊆ Set.range A.mulVec) ↔ (augment A (B a)).rank ≤ r) ∧
      ((augment A (B a)).rank ≤ r ↔ AllMinorsZero (r+1) (augment A (B a))) :=
  X7_cg_main n A B C r hrank hpos

end
