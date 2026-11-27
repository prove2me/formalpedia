-- Prove2me | solution 1 for TinyCoreset.Affine.theorem17_subspace_coreset
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:08:03.707161+00:00
-- url     : https://prove2.me/submissions/bfeda150-a47d-4343-92cd-094325f91b4d

import Theorems.Thm_TinyCoreset_DimRed_corollary16_subspace_coreset_bound
import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_Affine_Setting

set_option autoImplicit false

open TinyCoreset
open TinyCoreset.Affine

open scoped Matrix

open scoped InnerProductSpace
open TinyCoreset.DimRed

private theorem infDist_submodule {d : ℕ} (L : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) :
    Metric.infDist x (L : Set (EuclideanSpace ℝ (Fin d))) = ‖Lᗮ.orthogonalProjectionOnto x‖ := by
  let _ : Nonempty L.toAffineSubspace := ⟨⟨0, L.zero_mem⟩⟩
  change Metric.infDist x (L.toAffineSubspace : Set (EuclideanSpace ℝ (Fin d))) = _
  rw [← EuclideanGeometry.dist_orthogonalProjection_eq_infDist,
    EuclideanGeometry.orthogonalProjection_apply_mem _ (show (0 : EuclideanSpace ℝ (Fin d)) ∈ L.toAffineSubspace from L.zero_mem),
    dist_eq_norm_vsub]
  change ‖x - ((L.toAffineSubspace.direction.orthogonalProjectionOnto (x - 0) : EuclideanSpace ℝ (Fin d)) + 0)‖ = _
  rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.toAffineSubspace_direction,
    sub_zero, add_zero, ← Submodule.starProjection_orthogonal_val]
  rfl

private theorem orthogonal_coordinates {d j : ℕ} (L : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hL : Module.finrank ℝ L = j) :
    ∃ Y : Matrix (Fin d) (Fin (d - j)) ℝ, Yᵀ * Y = 1 ∧
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin d) ℝ),
        distSq A (L : Set (EuclideanSpace ℝ (Fin d))) = frobSq (A * Y) := by
  have dim : Module.finrank ℝ Lᗮ = d - j := by
    have h := L.finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace_fin, hL] at h
    omega
  let b := (stdOrthonormalBasis ℝ Lᗮ).reindex (finCongr dim)
  let Y : Matrix (Fin d) (Fin (d - j)) ℝ := Matrix.of fun i l => (b l : EuclideanSpace ℝ (Fin d)) i
  refine ⟨Y, ?_, ?_⟩
  · ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h := orthonormal_iff_ite.mp b.orthonormal i j
    change ⟪(b i : EuclideanSpace ℝ (Fin d)), (b j : EuclideanSpace ℝ (Fin d))⟫_ℝ = _ at h
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    change (∑ l, Y l i * Y l j) = _
    simpa [Y, dotProduct, mul_comm] using h
  · intro n A
    unfold distSq frobSq
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [infDist_submodule L, ← b.repr.norm_map, EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    rw [OrthonormalBasis.repr_apply_apply, Lᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left,
      EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply]
    simp [row, dotProduct, Y]

private theorem dist_smul_submodule {d : ℕ} (L : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    Metric.infDist (a • x) (L : Set (EuclideanSpace ℝ (Fin d))) ^ 2 =
      a ^ 2 * Metric.infDist x (L : Set (EuclideanSpace ℝ (Fin d))) ^ 2 := by
  rw [infDist_submodule L, infDist_submodule L, map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
open ProjLikeRetr.FixedRank

private theorem frob_trace {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    frobSq B = (Bᵀ * B).trace := by
  simp only [frobSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  exact Finset.sum_comm

private theorem frob_orthogonal_left {a b c : ℕ} (U : Matrix (Fin a) (Fin c) ℝ)
    (hU : Uᵀ * U = 1) (B : Matrix (Fin c) (Fin b) ℝ) :
    frobSq (U * B) = frobSq B := by
  rw [frob_trace, frob_trace, Matrix.transpose_mul, Matrix.mul_assoc Bᵀ Uᵀ (U * B),
    ← Matrix.mul_assoc Uᵀ U B, hU, Matrix.one_mul]

private def entries {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ) (i : Fin d) : ℝ :=
  if hi : (i : ℕ) < n then D ⟨i, hi⟩ i else 0

private theorem diag_gram {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ)
    (hD : ∀ (i : Fin n) (j : Fin d), (i : ℕ) ≠ (j : ℕ) → D i j = 0) :
    Dᵀ * D = Matrix.diagonal (fun i => entries D i ^ 2) := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq]
    by_cases hi : (i : ℕ) < n
    · rw [entries, dif_pos hi, Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
      · ring
      · intro k _ hk
        have hneq : (k : ℕ) ≠ (i : ℕ) := fun h => hk (Fin.ext h)
        rw [hD k i hneq, zero_mul]
      · simp
    · rw [entries, dif_neg hi, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      apply Finset.sum_eq_zero
      intro k _
      have hneq : (k : ℕ) ≠ (i : ℕ) := by omega
      rw [hD k i hneq, zero_mul]
  · rw [Matrix.diagonal_apply_ne _ hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : (k : ℕ) = (i : ℕ)
    · have hneq : (k : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext (hk.symm.trans h))
      rw [hD k j hneq, mul_zero]
    · rw [hD k i hk, zero_mul]

private theorem energy_diagonal {n d j : ℕ} (D : Matrix (Fin n) (Fin d) ℝ)
    (hD : ∀ (i : Fin n) (l : Fin d), (i : ℕ) ≠ (l : ℕ) → D i l = 0)
    (B : Matrix (Fin d) (Fin j) ℝ) :
    frobSq (D * B) = ∑ i : Fin d, entries D i ^ 2 * ∑ l : Fin j, B i l ^ 2 := by
  rw [frob_trace, Matrix.transpose_mul, Matrix.mul_assoc Bᵀ Dᵀ (D * B),
    ← Matrix.mul_assoc Dᵀ D B, Matrix.trace_mul_comm Bᵀ,
    Matrix.mul_assoc (Dᵀ * D) B Bᵀ, diag_gram D hD]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pow_two]

private def truncate {n d : ℕ} (m : ℕ) (S : Matrix (Fin n) (Fin d) ℝ) : Matrix (Fin n) (Fin d) ℝ :=
  Matrix.of (fun i j => if i.val = j.val ∧ i.val < m then S i j else 0)

private theorem truncate_diagonal {n d : ℕ} (m : ℕ) (S : Matrix (Fin n) (Fin d) ℝ) :
    ∀ (i : Fin n) (j : Fin d), (i : ℕ) ≠ (j : ℕ) → truncate m S i j = 0 := by
  intro i j hij
  simp [truncate, hij]

private theorem entries_truncate {n d : ℕ} (m : ℕ) (S : Matrix (Fin n) (Fin d) ℝ) (i : Fin d) :
    entries (truncate m S) i = if (i : ℕ) < m then entries S i else 0 := by
  by_cases hi : (i : ℕ) < n <;> simp [entries, hi, truncate]

private theorem tail_entry_le {n d : ℕ} {A U S V} (hA : IsSVD (n := n) (m := d) A U S V)
    (m : ℕ) (hm : m + 1 ≤ min n d) (i : Fin d) (hi : m ≤ (i : ℕ)) :
    entries S i ^ 2 ≤ sigma S (m + 1) ^ 2 := by
  have hmn : m < n := by omega
  have hmd : m < d := by omega
  by_cases hin : (i : ℕ) < n
  · rw [entries, dif_pos hin]
    have hs : sigma S (m + 1) = S ⟨m, hmn⟩ ⟨m, hmd⟩ := by
      simp [sigma, hm]
    rw [hs]
    apply sq_le_sq₀ (hA.2.2.2.1 _ _ rfl) (hA.2.2.2.1 _ _ rfl) |>.2
    exact hA.2.2.2.2.1 _ _ _ _ rfl rfl hi
  · simp [entries, hin, sq_nonneg]

private theorem frob_transpose {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    frobSq Bᵀ = frobSq B := by
  simp only [frobSq, Matrix.transpose_apply]
  exact Finset.sum_comm

private theorem frob_orthogonal_right {a b c : ℕ} (V : Matrix (Fin b) (Fin c) ℝ)
    (hV : Vᵀ * V = 1) (B : Matrix (Fin a) (Fin c) ℝ) :
    frobSq (B * Vᵀ) = frobSq B := by
  rw [← frob_transpose (B * Vᵀ), Matrix.transpose_mul, Matrix.transpose_transpose,
    frob_orthogonal_left V hV, frob_transpose]

private theorem weight_le_one {d j : ℕ} (B : Matrix (Fin d) (Fin j) ℝ) (hB : Bᵀ * B = 1)
    (i : Fin d) : ∑ l, B i l ^ 2 ≤ 1 := by
  let P := B * Bᵀ
  have hs (u v : Fin d) : P u v = P v u := by
    simp only [P, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hPP : P * P = P := by
    dsimp only [P]
    rw [Matrix.mul_assoc B Bᵀ (B * Bᵀ), ← Matrix.mul_assoc Bᵀ B Bᵀ, hB, Matrix.one_mul]
  have hx : P i i = ∑ l, B i l ^ 2 := by simp only [P, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  have hsquare : (P i i) ^ 2 ≤ P i i := by
    calc
      _ ≤ ∑ v, (P i v) ^ 2 := Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      _ = (P * P) i i := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun v _ => by rw [← hs i v, pow_two]
      _ = _ := by rw [hPP]
  rw [← hx]
  by_contra! h
  nlinarith [mul_pos (sub_pos.mpr h) (show 0 < P i i by linarith)]

private theorem entries_sub {n d : ℕ} (S T : Matrix (Fin n) (Fin d) ℝ) (i : Fin d) :
    entries (S - T) i = entries S i - entries T i := by
  by_cases hi : (i : ℕ) < n <;> simp [entries, hi, Matrix.sub_apply]

theorem solution {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ) (V : Matrix (Fin d) (Fin d) ℝ)
    (hA : ProjLikeRetr.FixedRank.IsSVD A U S V)
    (j : ℕ) (hj1 : 1 ≤ j) (ε : ℝ) (hε : 0 < ε) :
    coresetSize n d j ε + 1 ≤ j + ⌈(j : ℝ) / ε⌉₊ ∧
    0 ≤ TinyCoreset.DimRed.frobSq (A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ∧
    ∀ L : Submodule ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ L = j →
      TinyCoreset.DimRed.distSq A (L : Set (EuclideanSpace ℝ (Fin d))) ≤
          TinyCoreset.DimRed.wDistSq (fun _ => (1 : ℝ))
              (subspaceCoresetRows (coresetSize n d j ε) (coresetSize_le n d j ε) S V)
              (L : Set (EuclideanSpace ℝ (Fin d))) +
            TinyCoreset.DimRed.frobSq (A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ∧
        TinyCoreset.DimRed.wDistSq (fun _ => (1 : ℝ))
              (subspaceCoresetRows (coresetSize n d j ε) (coresetSize_le n d j ε) S V)
              (L : Set (EuclideanSpace ℝ (Fin d))) +
            TinyCoreset.DimRed.frobSq (A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ≤
          (1 + ε) * TinyCoreset.DimRed.distSq A (L : Set (EuclideanSpace ℝ (Fin d))) := by
  let m := coresetSize n d j ε
  have hbound : m + 1 ≤ j + ⌈(j : ℝ) / ε⌉₊ := by
    dsimp only [m, coresetSize]
    have hle := (min_le_right n (min d (j + ⌈(j : ℝ) / ε⌉₊ - 1))).trans (min_le_right _ _)
    omega
  have hnonneg : 0 ≤ frobSq (A - truncSVD m U S V) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  refine ⟨hbound, hnonneg, ?_⟩
  intro L hL
  obtain ⟨Y, hY, hdist⟩ := orthogonal_coordinates L hL
  have hunweighted (B : Matrix (Fin m) (Fin d) ℝ) :
      wDistSq (fun _ => (1 : ℝ)) B (L : Set (EuclideanSpace ℝ (Fin d))) =
        distSq B (L : Set (EuclideanSpace ℝ (Fin d))) := by simp [wDistSq, distSq]
  have hU : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)).mp hA.1
  let T := truncSigma m S * Vᵀ
  have row_zero (i : Fin n) (hi : ¬ (i : ℕ) < m) (l : Fin d) : T i l = 0 := by
    dsimp [T]
    rw [Matrix.mul_apply]
    simp [truncSigma, hi]
  have row_le (i : Fin n) (hi : ¬ (i : ℕ) < m) (l : Fin (d - j)) : (T * Y) i l = 0 := by
    rw [Matrix.mul_apply]
    simp [row_zero i hi]
  have rows_energy : frobSq (subspaceCoresetRows m (coresetSize_le n d j ε) S V * Y) = frobSq (T * Y) := by
    classical
    unfold frobSq
    have hrestrict : (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m),
        ∑ l, (T * Y) i l ^ 2) = ∑ i : Fin n, ∑ l, (T * Y) i l ^ 2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (i : ℕ) < m
      · simp [hi]
      · simp [hi, row_le i hi]
    rw [← hrestrict]
    refine Finset.sum_bij (fun (i : Fin m) _ => Fin.castLE (coresetSize_le n d j ε) i) ?_ ?_ ?_ ?_
    · intro i _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
    · intro i _ l _ heq
      exact Fin.ext (congrArg (fun x : Fin n => (x : ℕ)) heq)
    · intro i hi
      have hm := (Finset.mem_filter.mp hi).2
      exact ⟨⟨i, hm⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · intro i _
      rfl
  have tr_energy : frobSq (truncSVD m U S V * Y) = frobSq (T * Y) := by
    change frobSq ((U * truncSigma m S * Vᵀ) * Y) = _
    rw [Matrix.mul_assoc U (truncSigma m S) Vᵀ]
    change frobSq ((U * T) * Y) = _
    rw [Matrix.mul_assoc U T Y, frob_orthogonal_left U hU]
  rw [hunweighted, hdist, hdist, rows_energy, ← tr_energy]
  by_cases hfull : min n d ≤ m
  · have hcut : truncSigma m S = S := by
      ext i l
      by_cases hi : (i : ℕ) = (l : ℕ)
      · have hsmall : (i : ℕ) < m := by omega
        simp only [truncSigma, Matrix.of_apply, if_pos (And.intro hi hsmall)]
      · simp [truncSigma, hi, hA.2.2.1 i l hi]
    have hsame : truncSVD m U S V = A := by
      change U * truncSigma m S * Vᵀ = A
      rw [hcut, ← hA.2.2.2.2.2]
    rw [hsame, sub_self]
    have hzero : frobSq (0 : Matrix (Fin n) (Fin d) ℝ) = 0 := by simp [frobSq]
    rw [hzero, add_zero]
    refine ⟨le_rfl, ?_⟩
    have hnonneg : 0 ≤ frobSq (A * Y) :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    exact le_mul_of_one_le_left hnonneg (by linarith)
  · have hreal : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hceil := Nat.ceil_pos.mpr (div_pos hreal hε)
    have hm_eq : m = j + ⌈(j : ℝ) / ε⌉₊ - 1 := by
      dsimp only [m, coresetSize] at *
      omega
    have hrank : j + 1 ≤ d := by omega
    exact corollary16_subspace_coreset_bound A U S V hA j hj1 hrank ε hε m
      (by omega) (by omega) Y hY
