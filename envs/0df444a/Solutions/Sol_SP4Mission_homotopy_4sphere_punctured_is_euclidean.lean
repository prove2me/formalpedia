-- Prove2me | solution 1 for SP4Mission.homotopy_4sphere_punctured_is_euclidean
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-12T22:35:41.912926+00:00
-- url     : https://prove2.me/submissions/aa1aa31e-9f1b-4285-9253-8ac05b5fcdfa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SP4Sphere
import Theorems.Thm_SP4Mission_punctured_homotopy_sphere_smoothable
import Theorems.Thm_SP4Mission_punctured_almost_smooth_homotopy_sphere_homeomorph_euclidean

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

/-!
# A homotopy four-sphere is Euclidean away from a point (proof sketch)

Let `M` be a closed topological `4`-manifold homotopy equivalent to `S⁴`. Then for *every* point
`p ∈ M` (in particular for some point) the punctured manifold `M ∖ {p}` is homeomorphic to `ℝ⁴`.
This is the route of Freedman's proof of Theorem 1.6 (1982, p. 371):

* `SP4Mission.punctured_homotopy_sphere_smoothable` (Quinn): `M ∖ {p}` admits a smooth structure;
* `SP4Mission.punctured_almost_smooth_homotopy_sphere_homeomorph_euclidean` (Freedman,
  Corollary 1.2): the smooth, contractible, simply connected at infinity manifold `M ∖ {p}` is
  homeomorphic to `ℝ⁴`.

A point of `M` exists because `M` is homotopy equivalent to the nonempty space `S⁴`.
-/

/-- The target theorem. -/
theorem solution
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (hM : Nonempty (ContinuousMap.HomotopyEquiv M S4)) :
    ∃ (p : M), Nonempty ({x : M // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 4)) := by
  obtain ⟨e⟩ := id hM
  -- `S⁴` is nonempty, hence so is `M`.
  obtain ⟨s, hs⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin (4 + 1))) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  refine ⟨e.invFun ⟨s, hs⟩, ?_⟩
  -- Quinn: a smooth structure on the punctured manifold.
  obtain ⟨cs, hsm⟩ := punctured_homotopy_sphere_smoothable M hM (e.invFun ⟨s, hs⟩)
  -- Freedman, Corollary 1.2: the punctured manifold is homeomorphic to `ℝ⁴`.
  exact punctured_almost_smooth_homotopy_sphere_homeomorph_euclidean M hM (e.invFun ⟨s, hs⟩)
