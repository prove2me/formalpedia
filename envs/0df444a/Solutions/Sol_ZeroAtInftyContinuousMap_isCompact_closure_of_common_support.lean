-- Prove2me | solution 1 for ZeroAtInftyContinuousMap.isCompact_closure_of_common_support
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-18T17:04:24.506231+00:00
-- url     : https://prove2.me/submissions/40e156e2-8e52-4337-a9b4-b9a4e09e6e2e

import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

open Set
open scoped ZeroAtInfty BoundedContinuousFunction Topology

theorem solution {X : Type*} [TopologicalSpace X]
    (A : Set C₀(X, ℝ)) (K : Set X) (hK : IsCompact K)
    (hsupp : ∀ u ∈ A, ∀ x ∉ K, u x = 0)
    (M : ℝ) (hM : ∀ u ∈ A, ∀ x, |u x| ≤ M)
    (heq : Equicontinuous (fun u : A => (u.1 : X → ℝ))) :
    IsCompact (closure A) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let r : A → (K →ᵇ ℝ) := fun u =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x => u.1 x, u.1.continuous.comp continuous_subtype_val⟩
  have hr : Isometry r := by
    apply Isometry.of_dist_eq
    intro u v
    apply le_antisymm
    · apply (BoundedContinuousFunction.dist_le dist_nonneg).2
      intro x
      exact BoundedContinuousFunction.dist_coe_le_dist
        (f := u.1.toBCF) (g := v.1.toBCF) (x : X)
    · change dist u.1.toBCF v.1.toBCF ≤ dist (r u) (r v)
      apply (BoundedContinuousFunction.dist_le dist_nonneg).2
      intro x
      by_cases hx : x ∈ K
      · exact BoundedContinuousFunction.dist_coe_le_dist (f := r u) (g := r v) ⟨x, hx⟩
      · simp [hsupp u.1 u.2 x hx, hsupp v.1 v.2 x hx, dist_nonneg]
  have heqr : Equicontinuous (fun u : A => (r u : K → ℝ)) := by
    intro x
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    exact continuous_subtype_val.continuousAt
      (Metric.equicontinuousAt_iff_right.mp (heq x) ε hε)
  have hc : IsCompact (closure (range r)) := by
    apply BoundedContinuousFunction.arzela_ascoli (Set.Icc (-M) M) isCompact_Icc
    · rintro _ x ⟨u, rfl⟩
      exact abs_le.mp (hM u.1 u.2 x)
    · intro x
      rw [Metric.equicontinuousAt_iff_right]
      intro ε hε
      filter_upwards [Metric.equicontinuousAt_iff_right.mp (heqr x) ε hε] with y hy
      rintro ⟨g, u, rfl⟩
      exact hy u
  have ht : TotallyBounded (Set.univ : Set A) :=
    (totallyBounded_image_iff hr.isUniformInducing).mp
      (by simpa using hc.totallyBounded.subset subset_closure)
  have htA : TotallyBounded A := by
    simpa using ht.image isUniformEmbedding_subtype_val.uniformContinuous
  exact htA.closure.isCompact_of_isClosed isClosed_closure
