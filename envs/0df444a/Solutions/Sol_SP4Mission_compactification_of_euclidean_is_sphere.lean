-- Prove2me | solution 1 for SP4Mission.compactification_of_euclidean_is_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-11T14:46:40.024837+00:00
-- url     : https://prove2.me/submissions/3105fb61-35bd-4d00-883a-d6057dea145d

import Definitions.Def_SP4Sphere

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

theorem solution
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (p : M)
    (h : Nonempty ({x : M // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 4))) :
    Nonempty (M ≃ₜ S4) := by
  obtain ⟨e⟩ := h
  -- `M` is the one-point compactification of the punctured space `M \ {p}`.
  have hemb : Topology.IsEmbedding (Subtype.val : {x : M // x ≠ p} → M) :=
    Topology.IsEmbedding.subtypeVal
  have hrange : Set.range (Subtype.val : {x : M // x ≠ p} → M) = {p}ᶜ := by
    ext x; simp
  have h1 : OnePoint {x : M // x ≠ p} ≃ₜ M :=
    OnePoint.equivOfIsEmbeddingOfRangeEq p _ hemb hrange
  -- The one-point compactification of `ℝ⁴` is the standard `S⁴`.
  have h2 : OnePoint (EuclideanSpace ℝ (Fin 4)) ≃ₜ S4 :=
    onePointEquivSphereOfFinrankEq (by simp)
  exact ⟨h1.symm.trans (e.onePointCongr.trans h2)⟩
