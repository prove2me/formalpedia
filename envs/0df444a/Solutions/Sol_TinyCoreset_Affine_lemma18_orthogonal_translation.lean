-- Prove2me | solution 1 for TinyCoreset.Affine.lemma18_orthogonal_translation
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-26T23:37:01.343587+00:00
-- url     : https://prove2.me/submissions/07ce0791-3ce0-4e8a-a80a-b048c4332437

import Definitions.Def_TinyCoreset_Affine_Setting

set_option autoImplicit false

open scoped InnerProductSpace
open TinyCoreset.Affine TinyCoreset.DimRed

theorem solution {n d : ℕ} (M : Matrix (Fin n) (Fin d) ℝ)
    (hM : mean M = 0) (j : ℕ) (_hj1 : 1 ≤ j) (_hjd : j + 1 ≤ d)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (_hL : Module.finrank ℝ L = j)
    (t : EuclideanSpace ℝ (Fin d)) (ht : t ∈ Lᗮ) :
    distSq M (AffineSubspace.mk' t L : Set (EuclideanSpace ℝ (Fin d))) =
      distSq M (L : Set (EuclideanSpace ℝ (Fin d))) + (n : ℝ) * ‖t‖ ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp [distSq]
  let E := EuclideanSpace ℝ (Fin d)
  let residual (x : E) := x - L.starProjection x
  have hdist (x u : E) (hu : u ∈ Lᗮ) :
      Metric.infDist x (AffineSubspace.mk' u L : Set E) = ‖residual x - u‖ := by
    have hproj : L.starProjection u = 0 := by
      rw [Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hu,
        Submodule.coe_zero]
    rw [← EuclideanGeometry.dist_orthogonalProjection_eq_infDist,
      EuclideanGeometry.orthogonalProjection_apply_mem _ (AffineSubspace.self_mem_mk' u L),
      dist_eq_norm_vsub]
    change ‖x - (((AffineSubspace.mk' u L).direction.orthogonalProjectionOnto (x - u) : E) + u)‖ = _
    rw [Submodule.coe_orthogonalProjectionOnto_apply]
    simp only [AffineSubspace.direction_mk', map_sub, hproj, sub_zero, residual,
      sub_add_eq_sub_sub]
  have hzero : (AffineSubspace.mk' (0 : E) L : Set E) = (L : Set E) := by
    ext x
    change x - 0 ∈ L ↔ x ∈ L
    rw [sub_zero]
  have hdistZero (x : E) : Metric.infDist x (L : Set E) = ‖residual x‖ := by
    simpa only [hzero, sub_zero] using hdist x 0 (Lᗮ.zero_mem)
  have hrows : (∑ i, row M i) = (0 : E) := by
    apply WithLp.ofLp_injective
    funext k
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    change ∑ i, M i k = 0
    have hk := congrFun hM k
    change (1 / (n : ℝ)) * (∑ i, M i k) = 0 at hk
    exact (mul_eq_zero.mp hk).resolve_left (one_div_ne_zero (Nat.cast_ne_zero.mpr hn))
  have hresidual : (∑ i, residual (row M i)) = 0 := by
    simp only [residual, Finset.sum_sub_distrib, ← map_sum, hrows, map_zero, sub_zero]
  simp_rw [distSq, hdist _ t ht, hdistZero, norm_sub_sq_real]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_inner,
    hresidual, inner_zero_left, mul_zero, sub_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
