-- Prove2me | solution 1 for TinyCoreset.Affine.theorem19_affine_subspace_coreset
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:13:02.929269+00:00
-- url     : https://prove2.me/submissions/352695b3-a52d-4d00-8c56-2cba477e71fc

import Theorems.Thm_TinyCoreset_Affine_theorem17_subspace_coreset
import Theorems.Thm_TinyCoreset_Affine_lemma18_orthogonal_translation
import Theorems.Thm_TinyCoreset_Affine_eq7_symmetrized_coreset
import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_Affine_Setting

set_option autoImplicit false

open TinyCoreset
open TinyCoreset.Affine
open TinyCoreset.DimRed ProjLikeRetr.FixedRank

open scoped Matrix

theorem solution {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ) (V : Matrix (Fin d) (Fin d) ℝ)
    (hA : ProjLikeRetr.FixedRank.IsSVD (center A) U S V) (hn : 1 ≤ n)
    (j : ℕ) (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    coresetSize n d j ε + 1 ≤ j + ⌈(j : ℝ) / ε⌉₊ ∧
    0 ≤ TinyCoreset.DimRed.frobSq (center A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ∧
    ∀ C : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ C.direction = j →
      (C : Set (EuclideanSpace ℝ (Fin d))).Nonempty →
      TinyCoreset.DimRed.distSq A (C : Set (EuclideanSpace ℝ (Fin d))) ≤
          TinyCoreset.DimRed.wDistSq (fun _ => affineWeight n (coresetSize n d j ε))
              (affineCoresetRows n (mean A)
                (subspaceCoresetRows (coresetSize n d j ε) (coresetSize_le n d j ε) S V))
              (C : Set (EuclideanSpace ℝ (Fin d))) +
            TinyCoreset.DimRed.frobSq (center A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ∧
        TinyCoreset.DimRed.wDistSq (fun _ => affineWeight n (coresetSize n d j ε))
              (affineCoresetRows n (mean A)
                (subspaceCoresetRows (coresetSize n d j ε) (coresetSize_le n d j ε) S V))
              (C : Set (EuclideanSpace ℝ (Fin d))) +
            TinyCoreset.DimRed.frobSq (center A - ProjLikeRetr.FixedRank.truncSVD (coresetSize n d j ε) U S V) ≤
          (1 + ε) * TinyCoreset.DimRed.distSq A (C : Set (EuclideanSpace ℝ (Fin d))) := by
  let E := EuclideanSpace ℝ (Fin d)
  let m := coresetSize n d j ε
  let μ : E := WithLp.toLp 2 (mean A)
  let S' := subspaceCoresetRows m (coresetSize_le n d j ε) S V
  let S'' := affineCoresetRows n 0 S'
  let Sfinal := affineCoresetRows n (mean A) S'
  let α := affineWeight n m
  let Δ := frobSq (center A - truncSVD m U S V)
  have theorem17 := theorem17_subspace_coreset (center A) U S V hA j hj1 ε hε
  refine ⟨theorem17.1, theorem17.2.1, ?_⟩
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : 0 < m := by
    have hj : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hceil := Nat.ceil_pos.mpr (div_pos hj hε)
    dsimp [m, coresetSize]
    omega
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have halpha : 0 ≤ α := div_nonneg hnreal.le (by positivity)
  have hmass : α * ((m + m : ℕ) : ℝ) = (n : ℝ) := by
    simp only [α, affineWeight, Nat.cast_add]
    field_simp [hmreal.ne']
    ring
  have hcenter : mean (center A) = 0 := by
    funext l
    simp only [mean, center, Matrix.of_apply, Pi.zero_apply, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hnreal.ne']
    ring
  have hsym : mean S'' = 0 := by
    funext l
    unfold mean
    rw [Fin.sum_univ_add]
    simp only [S'', affineCoresetRows, Fin.append_left, Fin.append_right, Pi.zero_apply,
      zero_add, zero_sub, Finset.sum_neg_distrib, add_neg_cancel, mul_zero]
  have hrow (i : Fin n) : row A i - μ = row (center A) i := by
    ext l
    rfl
  have hrowS (i : Fin (m + m)) : row Sfinal i - μ = row S'' i := by
    ext l
    change Sfinal i l - mean A l = S'' i l
    induction i using Fin.addCases
    · simp only [Sfinal, S'', affineCoresetRows, Fin.append_left, Pi.zero_apply, zero_add]
      ring
    · simp only [Sfinal, S'', affineCoresetRows, Fin.append_right, Pi.zero_apply, zero_sub]
      ring
  intro C hCdim hC
  let L := C.direction
  obtain ⟨p, hp⟩ := hC
  let u := p - μ
  let t := u - L.starProjection u
  have ht : t ∈ Lᗮ := L.sub_starProjection_mem_orthogonal u
  have htC : μ + t ∈ C := by
    have hneg : -(L.starProjection u) ∈ C.direction := L.neg_mem (L.starProjection_apply_mem u)
    have hv := C.vadd_mem_of_mem_direction hneg hp
    change -(L.starProjection u) + p ∈ C at hv
    convert hv using 1
    dsimp [t, u]
    abel
  let D : AffineSubspace ℝ E := AffineSubspace.mk' t L
  have htranslate : (fun y : E => y - μ) '' (C : Set E) = (D : Set E) := by
    have hCmk : AffineSubspace.mk' (μ + t) L = C := AffineSubspace.mk'_eq htC
    rw [← hCmk]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change y - (μ + t) ∈ L at hy
      change y - μ - t ∈ L
      rwa [sub_sub]
    · intro hx
      change x - t ∈ L at hx
      refine ⟨x + μ, ?_, add_sub_cancel_right x μ⟩
      change x + μ - (μ + t) ∈ L
      convert hx using 1
      abel
  have iso : Isometry (fun y : E => y - μ) := by
    apply Isometry.of_dist_eq
    intro x y
    simp [dist_eq_norm]
  have distance (x : E) : Metric.infDist x (C : Set E) = Metric.infDist (x - μ) (D : Set E) := by
    rw [← htranslate, Metric.infDist_image iso]
  have input_translation : distSq A (C : Set E) = distSq (center A) (D : Set E) := by
    unfold distSq
    exact Finset.sum_congr rfl fun i _ => by rw [distance, hrow]
  have output_translation : wDistSq (fun _ => α) Sfinal (C : Set E) = α * distSq S'' (D : Set E) := by
    unfold wDistSq distSq
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [distance, hrowS]
  have input_cost : distSq (center A) (D : Set E) = distSq (center A) (L : Set E) + (n : ℝ) * ‖t‖ ^ 2 :=
    lemma18_orthogonal_translation (center A) hcenter j hj1 hjd L hCdim t ht
  have output_cost : distSq S'' (D : Set E) = distSq S'' (L : Set E) + ((m+m : ℕ) : ℝ) * ‖t‖ ^ 2 :=
    lemma18_orthogonal_translation S'' hsym j hj1 hjd L hCdim t ht
  have bound := eq7_symmetrized_coreset A U S V hA hn j hj1 hjd ε hε L hCdim
  change distSq (center A) (L : Set E) ≤ α * distSq S'' (L : Set E) + Δ ∧
      α * distSq S'' (L : Set E) + Δ ≤ (1 + ε) * distSq (center A) (L : Set E) at bound
  change distSq A (C : Set E) ≤ wDistSq (fun _ => α) Sfinal (C : Set E) + Δ ∧
      wDistSq (fun _ => α) Sfinal (C : Set E) + Δ ≤ (1 + ε) * distSq A (C : Set E)
  rw [input_translation, output_translation, input_cost, output_cost, mul_add, ← mul_assoc, hmass]
  obtain ⟨lower, upper⟩ := bound
  have extra : 0 ≤ ε * ((n : ℝ) * ‖t‖ ^ 2) := by positivity
  constructor <;> linarith
