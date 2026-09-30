-- Prove2me | solution 1 for SP4Mission.freedman_poincare_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-08T04:11:54.285055+00:00
-- url     : https://prove2.me/submissions/bef5b750-780a-459d-9387-eb918594aec3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SP4Sphere
import Theorems.Thm_SP4Mission_punctured_homotopy_sphere_smoothable
import Theorems.Thm_SP4Mission_punctured_almost_smooth_homotopy_sphere_homeomorph_euclidean

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

/-!
Freedman's topological four-dimensional Poincaré theorem, reduced to its two
theorem-level inputs (Freedman 1982, proof of Theorem 1.6, p. 371, and the
uniqueness proof of Theorem 1.5, pp. 370–371):

1. `punctured_homotopy_sphere_smoothable`: a punctured homotopy 4-sphere carries a
   smooth structure (the homotopy sphere is "almost smooth");
2. `punctured_almost_smooth_homotopy_sphere_homeomorph_euclidean`: a punctured
   almost-smooth homotopy 4-sphere is homeomorphic to `ℝ⁴` (the `ω = 0` case of the
   uniqueness part of Theorem 1.5, via the proper h-cobordism theorem).

The remaining step — "this gives a homeomorphism of `M - pt` to `M' - pt` which extends to
the 1-point compactification `M ≅ M'`" — is carried out below: `M` is the one-point
compactification of `M ∖ {p}`, and the one-point compactification of `ℝ⁴` is `S⁴`.
-/

theorem solution
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] :
    Nonempty (ContinuousMap.HomotopyEquiv M S4) → Nonempty (M ≃ₜ S4) := by
  intro hM
  -- Step 0: `M` is nonempty — pull a point of `S⁴` back along the homotopy inverse.
  obtain ⟨f⟩ := id hM
  have hS4 : Nonempty S4 :=
    ⟨⟨EuclideanSpace.single (0 : Fin (4 + 1)) (1 : ℝ), by simp⟩⟩
  let p : M := f.invFun hS4.some
  -- Step 1 (Freedman, proof of Thm 1.6): smooth `M ∖ {p}`.
  obtain ⟨_cs, _hcs⟩ := punctured_homotopy_sphere_smoothable M hM p
  -- Step 2 (Freedman, Thm 1.5 uniqueness, `ω = 0`): `M ∖ {p} ≅ ℝ⁴`.
  obtain ⟨e⟩ := punctured_almost_smooth_homotopy_sphere_homeomorph_euclidean M hM p
  -- Step 3: extend over the point via one-point compactifications.
  have hrange : Set.range (Subtype.val : {x : M // x ≠ p} → M) = {p}ᶜ := by
    ext x
    simp
  let h₁ : OnePoint {x : M // x ≠ p} ≃ₜ M :=
    OnePoint.equivOfIsEmbeddingOfRangeEq p Subtype.val Topology.IsEmbedding.subtypeVal hrange
  let h₂ : OnePoint {x : M // x ≠ p} ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 4)) :=
    e.onePointCongr
  let h₃ : OnePoint (EuclideanSpace ℝ (Fin 4)) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (4 + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  exact ⟨(h₁.symm.trans h₂).trans h₃⟩
