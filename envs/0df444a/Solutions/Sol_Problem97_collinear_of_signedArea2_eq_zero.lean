-- Prove2me | solution 1 for Problem97.collinear_of_signedArea2_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:50.406114+00:00
-- url     : https://prove2.me/submissions/40edc5e3-ff9d-43b4-9a94-3ae5aa96f30a

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.Moser.NonDeg:4270:5462. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Theorems.Thm_Problem97_signedArea2_eq_zero_exists_smul

section Erdos9796CountingFragment_Erdos9796Proof_P97_Moser_NonDeg

open Problem97

/- Fragment from Erdos9796Proof.P97.Moser.NonDeg; source SHA-256 dd0335fd4a8de1d4d259bdc5a1fcac46e7a179fe1304481d159a516764ebdac7 -/


/-!
# Moser triangle vertices are noncollinear: nonzero signed area

The circumscribed branch of `Problem97.MEC.MoserTriangle` carries three
pairwise distinct `A`-vertices on the MEC boundary. This file proves that
those three vertices have nonzero `signedArea2`, which the downstream
cap-partition consumer (`Problem97.MEC.cap_partition_from_moser_circumscribed`)
needs to discharge its `hMoserNonDeg` hypothesis.

## Mathematical content

Three distinct points equidistant from a common center cannot be
collinear: a line meets a circle in at most two points. We package
this via Mathlib's strict-convex-space machinery:

* If three collinear points lie on a circle, one is `Wbtw` of the other
  two by `Collinear.wbtw_or_wbtw_or_wbtw`. With pairwise distinctness
  this strengthens to `Sbtw`, and `Sbtw.dist_lt_max_dist` gives a
  strictly smaller distance to the center — contradicting equidistance.

To translate to `signedArea2`, we prove
`signedArea2 v1 v2 v3 = 0 → Collinear ℝ {v1, v2, v3}` directly from the
2D cross-product identity (case analysis on which coordinate of
`v2 - v1` is nonzero, picking the scalar accordingly).

## Main declarations

* `Problem97.collinear_of_signedArea2_eq_zero` — algebraic predicate
  `signedArea2 = 0` implies the three points are collinear.
* `Problem97.MEC.not_collinear_of_three_dist_eq` — three distinct
  equidistant points are noncollinear (uses `StrictConvexSpace ℝ ℝ²`).
* `Problem97.MEC.signedArea2_ne_zero_of_three_dist_eq` — combining the
  two: three distinct equidistant points have nonzero signed area.
* `Problem97.MEC.moser_triangle_signed_area_ne_zero` — the target
  theorem applied to the circumscribed branch of `MoserTriangle`.
-/

open scoped EuclideanGeometry
open Finset






theorem solution (v1 v2 v3 : ℝ²)
    (h : signedArea2 v1 v2 v3 = 0) :
    Collinear ℝ ({v1, v2, v3} : Set ℝ²) := by
  rw [collinear_iff_of_mem (p₀ := v1) (Set.mem_insert _ _)]
  by_cases h21 : v2 = v1
  · -- Degenerate case: `v2 = v1`. Use `v3 - v1` as the line direction.
    refine ⟨v3 - v1, ?_⟩
    intro p hp
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · rw [h21]
      exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  · -- Nondegenerate: use `v2 - v1` as the direction; scalar for `v3`
    -- comes from `signedArea2_eq_zero_exists_smul`.
    refine ⟨v2 - v1, ?_⟩
    intro p hp
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · obtain ⟨r, hr⟩ := signedArea2_eq_zero_exists_smul h21 h
      refine ⟨r, ?_⟩
      rw [eq_vadd_iff_vsub_eq, vsub_eq_sub]
      exact hr

end Erdos9796CountingFragment_Erdos9796Proof_P97_Moser_NonDeg
