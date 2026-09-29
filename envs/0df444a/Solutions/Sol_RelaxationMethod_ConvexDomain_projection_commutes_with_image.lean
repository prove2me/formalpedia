-- Prove2me | solution 1 for RelaxationMethod.ConvexDomain.projection_commutes_with_image
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:02:02.060242+00:00
-- url     : https://prove2.me/submissions/42264239-de9c-4a6d-bf23-d8282f9c063a

import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess



namespace RelaxationMethod.ConvexDomain

theorem pc_pyth {n : ℕ} (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) [Nonempty L]
    (p x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ L) :
    dist p x ^ 2 = dist p (EuclideanGeometry.orthogonalProjection L p) ^ 2 +
      dist (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) x ^ 2 := by
  have := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    p hx (s := L)
  rw [dist_comm x p, dist_comm x] at this
  rw [sq, sq, sq, this]; ring

theorem pc_infDist {n : ℕ} (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) [Nonempty L]
    (p : EuclideanSpace ℝ (Fin n)) :
    Metric.infDist p (L : Set (EuclideanSpace ℝ (Fin n))) =
      dist p (EuclideanGeometry.orthogonalProjection L p) := by
  apply le_antisymm (Metric.infDist_le_dist_of_mem (EuclideanGeometry.orthogonalProjection_mem p))
  rw [Metric.le_infDist ⟨_, EuclideanGeometry.orthogonalProjection_mem p⟩]
  intro x hx
  have := pc_pyth L p x hx
  have h2 : dist p (EuclideanGeometry.orthogonalProjection L p) ^ 2 ≤ dist p x ^ 2 := by
    rw [this]; nlinarith [sq_nonneg (dist (EuclideanGeometry.orthogonalProjection L p :
      EuclideanSpace ℝ (Fin n)) x)]
  exact (pow_le_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero).mp h2

theorem pc_core {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) [Nonempty L] (hAL : A ⊆ L)
    (p p₁ : EuclideanSpace ℝ (Fin n)) :
    (∀ q ∈ A, ((∀ a ∈ A, dist p q ≤ dist p a) ↔
      (∀ a ∈ A, dist (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) q ≤
        dist (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) a))) ∧
    (IsImage A p p₁ →
      IsImage A (EuclideanGeometry.orthogonalProjection L p)
          (EuclideanGeometry.orthogonalProjection L p₁) ∧
        p₁ - (EuclideanGeometry.orthogonalProjection L p₁ : EuclideanSpace ℝ (Fin n)) =
          -(p - (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n))) ∧
        Metric.infDist p₁ (L : Set (EuclideanSpace ℝ (Fin n))) =
          Metric.infDist p (L : Set (EuclideanSpace ℝ (Fin n)))) := by
  set P : EuclideanSpace ℝ (Fin n) := (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) with hP
  have hPL : P ∈ L := EuclideanGeometry.orthogonalProjection_mem p
  have hiff : ∀ q ∈ A, ((∀ a ∈ A, dist p q ≤ dist p a) ↔ (∀ a ∈ A, dist P q ≤ dist P a)) := by
    intro q hq
    constructor
    · intro h a ha
      have h1 := pc_pyth L p q (hAL hq)
      have h2 := pc_pyth L p a (hAL ha)
      have h3 := h a ha
      have h4 : dist p q ^ 2 ≤ dist p a ^ 2 := pow_le_pow_left₀ dist_nonneg h3 2
      rw [← hP] at h1 h2
      have h5 : dist P q ^ 2 ≤ dist P a ^ 2 := by linarith
      exact (pow_le_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero).mp h5
    · intro h a ha
      have h1 := pc_pyth L p q (hAL hq)
      have h2 := pc_pyth L p a (hAL ha)
      have h3 := h a ha
      have h4 : dist P q ^ 2 ≤ dist P a ^ 2 := pow_le_pow_left₀ dist_nonneg h3 2
      rw [← hP] at h1 h2
      have h5 : dist p q ^ 2 ≤ dist p a ^ 2 := by linarith
      exact (pow_le_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero).mp h5
  refine ⟨hiff, ?_⟩
  rintro ⟨q, ⟨hqA, hqn⟩, hp₁⟩
  have hqL : q ∈ L := hAL hqA
  have hmem : (2 : ℝ) • (q - P) + P ∈ L := by
    have := AffineSubspace.smul_vsub_vadd_mem L (2 : ℝ) hqL hPL hPL
    simpa using this
  have hperp : P - p ∈ L.directionᗮ :=
    EuclideanGeometry.orthogonalProjection_vsub_mem_direction_orthogonal L p
  have hproj : (EuclideanGeometry.orthogonalProjection L p₁ : EuclideanSpace ℝ (Fin n)) =
      (2 : ℝ) • (q - P) + P := by
    have e : p₁ = (P - p) +ᵥ ((2 : ℝ) • (q - P) + P) := by
      rw [hp₁, vadd_eq_add]; module
    rw [e, EuclideanGeometry.orthogonalProjection_vadd_eq_self hmem hperp]
  have hdiff : p₁ - (EuclideanGeometry.orthogonalProjection L p₁ : EuclideanSpace ℝ (Fin n)) =
      -(p - P) := by
    rw [hproj, hp₁]; module
  refine ⟨⟨q, ⟨hqA, (hiff q hqA).mp hqn⟩, ?_⟩, hdiff, ?_⟩
  · rw [hproj]; module
  · rw [pc_infDist, pc_infDist, dist_eq_norm, dist_eq_norm, hdiff, norm_neg]

end RelaxationMethod.ConvexDomain

open RelaxationMethod.ConvexDomain


theorem solution {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A)
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) [Nonempty L] (hAL : A ⊆ L)
    (p p₁ : EuclideanSpace ℝ (Fin n)) :
    (∀ q ∈ A, ((∀ a ∈ A, dist p q ≤ dist p a) ↔
      (∀ a ∈ A, dist (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) q ≤
        dist (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) a))) ∧
    (IsImage A p p₁ →
      IsImage A (EuclideanGeometry.orthogonalProjection L p)
          (EuclideanGeometry.orthogonalProjection L p₁) ∧
        p₁ - (EuclideanGeometry.orthogonalProjection L p₁ : EuclideanSpace ℝ (Fin n)) =
          -(p - (EuclideanGeometry.orthogonalProjection L p : EuclideanSpace ℝ (Fin n))) ∧
        Metric.infDist p₁ (L : Set (EuclideanSpace ℝ (Fin n))) =
          Metric.infDist p (L : Set (EuclideanSpace ℝ (Fin n)))) := by
  exact pc_core A L hAL p p₁
