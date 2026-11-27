-- Prove2me | solution 1 for TinyCoreset.Affine.eq7_symmetrized_coreset
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:11:02.304243+00:00
-- url     : https://prove2.me/submissions/611eddf5-c061-475f-a217-a960085855a3

import Theorems.Thm_TinyCoreset_Affine_theorem17_subspace_coreset
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

theorem solution {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ) (V : Matrix (Fin d) (Fin d) ℝ)
    (hA : ProjLikeRetr.FixedRank.IsSVD (center A) U S V) (hn : 1 ≤ n)
    (j : ℕ) (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∀ L : Submodule ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ L = j →
      TinyCoreset.DimRed.distSq (center A) (L : Set (EuclideanSpace ℝ (Fin d))) ≤
          affineWeight n (coresetSize n d j ε) *
              TinyCoreset.DimRed.distSq (affineCoresetRows n 0
                  (subspaceCoresetRows (coresetSize n d j ε) (coresetSize_le n d j ε) S V))
                (L : Set (EuclideanSpace ℝ (Fin d))) +
            TinyCoreset.DimRed.frobSq (center A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ∧
        affineWeight n (coresetSize n d j ε) *
              TinyCoreset.DimRed.distSq (affineCoresetRows n 0
                  (subspaceCoresetRows (coresetSize n d j ε) (coresetSize_le n d j ε) S V))
                (L : Set (EuclideanSpace ℝ (Fin d))) +
            TinyCoreset.DimRed.frobSq (center A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ≤
          (1 + ε) * TinyCoreset.DimRed.distSq (center A) (L : Set (EuclideanSpace ℝ (Fin d))) := by
  intro L hL
  let m := coresetSize n d j ε
  let S' := subspaceCoresetRows m (coresetSize_le n d j ε) S V
  let γ := Real.sqrt ((m : ℝ) / (n : ℝ))
  have hm : 0 < m := by
    have hj : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hceil := Nat.ceil_pos.mpr (div_pos hj hε)
    dsimp [m, coresetSize]
    omega
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have row_left (i : Fin m) : row (affineCoresetRows n 0 S') (Fin.castAdd m i) = γ • row S' i := by
    ext l
    simp [row, affineCoresetRows, γ]
  have row_right (i : Fin m) : row (affineCoresetRows n 0 S') (Fin.natAdd m i) = (-γ) • row S' i := by
    ext l
    change (Fin.append (fun (i : Fin m) l => (0 : Fin d → ℝ) l + γ * S' i l)
      (fun i l => (0 : Fin d → ℝ) l - γ * S' i l) (Fin.natAdd m i)) l = (-γ) * S' i l
    rw [Fin.append_right]
    simp only [Pi.zero_apply, zero_sub, neg_mul]
  have scale : affineWeight n m * distSq (affineCoresetRows n 0 S') (L : Set (EuclideanSpace ℝ (Fin d))) =
      wDistSq (fun _ => (1 : ℝ)) S' (L : Set (EuclideanSpace ℝ (Fin d))) := by
    unfold distSq wDistSq
    rw [Fin.sum_univ_add]
    simp only [row_left, row_right, dist_smul_submodule, neg_sq, one_mul, ← Finset.mul_sum]
    have hsq : γ ^ 2 = (m : ℝ) / (n : ℝ) := Real.sq_sqrt (by positivity)
    rw [hsq, affineWeight]
    field_simp [hnreal.ne', hmreal.ne']
    ring
  have h := (theorem17_subspace_coreset (center A) U S V hA j hj1 ε hε).2.2 L hL
  change distSq (center A) (L : Set (EuclideanSpace ℝ (Fin d))) ≤
      affineWeight n m * distSq (affineCoresetRows n 0 S') (L : Set (EuclideanSpace ℝ (Fin d))) +
        frobSq (center A - ProjLikeRetr.FixedRank.truncSVD m U S V) ∧
      affineWeight n m * distSq (affineCoresetRows n 0 S') (L : Set (EuclideanSpace ℝ (Fin d))) +
        frobSq (center A - ProjLikeRetr.FixedRank.truncSVD m U S V) ≤
      (1 + ε) * distSq (center A) (L : Set (EuclideanSpace ℝ (Fin d)))
  rw [scale]
  exact h
