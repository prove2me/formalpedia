-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.free_lens_subgroups
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:14:32.788107+00:00
-- url     : https://prove2.me/submissions/cf286a91-fcc3-4596-899b-c08f1912a90a

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41
noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4FreeLens

open QAlgorithms.Papers.Independent.Claimed50.P41

/-- Hausdorff dimension of a translate of the range of an injective linear map. -/
lemma dimH_range_affine {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (ι → ℝ) →ₗ[ℝ] F) (hL : Function.Injective L) (c : F) :
    dimH (Set.range fun x => c + L x) = (Fintype.card ι : ℝ≥0∞) := by
  have h1 : (Set.range fun x => c + L x) =
      (fun y => c + y) '' (((↑) : LinearMap.range L → F) '' Set.univ) := by
    ext y; simp only [Set.mem_range, Set.image_univ, Subtype.range_coe_subtype, Set.mem_image,
      LinearMap.mem_range]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨L x, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
  rw [h1, (isometry_add_left c).dimH_image, isometry_subtype_coe.dimH_image,
    Real.dimH_univ_eq_finrank, LinearMap.finrank_range_of_inj hL,
    Module.finrank_fintype_fun_eq_card]

lemma card_sym2_fin (n : ℕ) : Fintype.card (Sym2 (Fin n)) = n * (n + 1) / 2 := by
  rw [Sym2.card, Fintype.card_fin, Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]

/-- The symmetric matrix attached to a function on unordered pairs. -/
def symOf {n : ℕ} (c : Sym2 (Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => c s(i, j)

def symOfLin (n : ℕ) : (Sym2 (Fin n) → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun := symOf
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma symOf_isSymm {n : ℕ} (c : Sym2 (Fin n) → ℝ) : (symOf c).IsSymm := by
  ext i j; simp [symOf, Matrix.transpose_apply, Sym2.eq_swap]

lemma exists_symOf {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    ∃ c, symOf c = B := by
  refine ⟨Sym2.lift ⟨fun i j => B i j, fun i j => ?_⟩, ?_⟩
  · exact (hB.apply j i)
  · ext i j; simp [symOf]

lemma symOf_injective (n : ℕ) : Function.Injective (@symOf n) := by
  intro c d h
  funext z
  induction z using Sym2.ind with
  | _ i j => exact congrFun (congrFun h i) j

lemma set_eq_range {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ → Matrix (Phase n) (Phase n) ℝ) :
    {M | ∃ B, B.IsSymm ∧ M = f B} = Set.range (fun c => f (symOf c)) := by
  ext M
  constructor
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨c, rfl⟩ := exists_symOf B hB
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, symOf_isSymm c, rfl⟩

def freePart (n : ℕ) : (Sym2 (Fin n) → ℝ) →ₗ[ℝ] Matrix (Phase n) (Phase n) ℝ where
  toFun c := Matrix.fromBlocks 0 (symOf c) 0 0
  map_add' a b := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [symOf]
  map_smul' r a := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [symOf]

def lensPart (n : ℕ) : (Sym2 (Fin n) → ℝ) →ₗ[ℝ] Matrix (Phase n) (Phase n) ℝ where
  toFun c := Matrix.fromBlocks 0 0 (symOf c) 0
  map_add' a b := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [symOf]
  map_smul' r a := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [symOf]

lemma freePart_inj (n : ℕ) : Function.Injective (freePart n) := by
  intro a b h
  apply symOf_injective
  ext i j
  have := congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
  simpa [freePart] using this

lemma lensPart_inj (n : ℕ) : Function.Injective (lensPart n) := by
  intro a b h
  apply symOf_injective
  ext i j
  have := congrFun (congrFun h (Sum.inr i)) (Sum.inl j)
  simpa [lensPart] using this

lemma free_eq (n : ℕ) (c : Sym2 (Fin n) → ℝ) :
    freeMatrix (symOf c) = (1 : Matrix (Phase n) (Phase n) ℝ) + freePart n c := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;>
    simp [freeMatrix, freePart, Matrix.one_apply, Matrix.fromBlocks]

lemma lens_eq (n : ℕ) (c : Sym2 (Fin n) → ℝ) :
    lensMatrix (symOf c) = (1 : Matrix (Phase n) (Phase n) ℝ) + lensPart n c := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;>
    simp [lensMatrix, lensPart, Matrix.one_apply, Matrix.fromBlocks]

lemma sigma_mul_neg (n : ℕ) : sigma n * (-sigma n) = 1 := by
  simp only [sigma, Matrix.mul_neg, Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one]

lemma sigma_inv (n : ℕ) : (sigma n)⁻¹ = -sigma n :=
  Matrix.inv_eq_right_inv (sigma_mul_neg n)

end X4FreeLens

open X4FreeLens QAlgorithms.Papers.Independent.Claimed50.P41 in
theorem solution (n : ℕ) (hn : 0 < n) :
    (∀ B : Matrix (Fin n) (Fin n) ℝ,
      (PreservesCanonicalForm (freeMatrix B) ↔ B.IsSymm) ∧
      (PreservesCanonicalForm (lensMatrix B) ↔ B.IsSymm)) ∧
    (∀ B C : Matrix (Fin n) (Fin n) ℝ,
      freeMatrix B * freeMatrix C = freeMatrix (B + C) ∧
      lensMatrix B * lensMatrix C = lensMatrix (B + C) ∧
      freeMatrix B * freeMatrix C = freeMatrix C * freeMatrix B ∧
      lensMatrix B * lensMatrix C = lensMatrix C * lensMatrix B ∧
      sigma n * freeMatrix B * (sigma n)⁻¹ = lensMatrix (-B)) ∧
    (∀ (B : Matrix (Fin n) (Fin n) ℝ) (z : Phase n → ℝ) (i : Fin n),
      (Matrix.mulVec (freeMatrix B) z) (Sum.inl i) = z (Sum.inl i) + ∑ j, B i j * z (Sum.inr j) ∧
      (Matrix.mulVec (freeMatrix B) z) (Sum.inr i) = z (Sum.inr i) ∧
      (Matrix.mulVec (lensMatrix B) z) (Sum.inl i) = z (Sum.inl i) ∧
      (Matrix.mulVec (lensMatrix B) z) (Sum.inr i) = z (Sum.inr i) + ∑ j, B i j * z (Sum.inl j)) ∧
    dimH {M : Matrix (Phase n) (Phase n) ℝ | ∃ B, B.IsSymm ∧ M = freeMatrix B} =
      (n * (n + 1) / 2 : ℕ) ∧
    dimH {M : Matrix (Phase n) (Phase n) ℝ | ∃ C, C.IsSymm ∧ M = lensMatrix C} =
      (n * (n + 1) / 2 : ℕ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro B
    constructor
    · unfold PreservesCanonicalForm freeMatrix sigma
      rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp only [Matrix.fromBlocks_inj]
      simp [Matrix.IsSymm, neg_add_eq_zero, eq_comm]
    · unfold PreservesCanonicalForm lensMatrix sigma
      rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp only [Matrix.fromBlocks_inj]
      simp [Matrix.IsSymm, neg_add_eq_zero]
  · intro B C
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [freeMatrix, Matrix.fromBlocks_multiply, add_comm]
    · simp [lensMatrix, Matrix.fromBlocks_multiply]
    · simp [freeMatrix, Matrix.fromBlocks_multiply, add_comm]
    · simp [lensMatrix, Matrix.fromBlocks_multiply, add_comm]
    · rw [sigma_inv]
      simp [freeMatrix, lensMatrix, sigma, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]
  · intro B z i
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [freeMatrix, lensMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.one_apply, add_comm]
  · rw [set_eq_range, ← card_sym2_fin]
    simp_rw [free_eq]
    exact dimH_range_affine _ (freePart_inj n) 1
  · rw [set_eq_range, ← card_sym2_fin]
    simp_rw [lens_eq]
    exact dimH_range_affine _ (lensPart_inj n) 1
