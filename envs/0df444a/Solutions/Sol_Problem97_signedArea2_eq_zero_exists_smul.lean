-- Prove2me | solution 1 for Problem97.signedArea2_eq_zero_exists_smul
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:24.486626+00:00
-- url     : https://prove2.me/submissions/42cab6bc-f39f-4e8f-89af-e10bf9f61fdd

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.Moser.NonDeg:1830:4268. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation

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




theorem solution {v1 v2 v3 : ℝ²}
    (h21 : v2 ≠ v1) (h : signedArea2 v1 v2 v3 = 0) :
    ∃ r : ℝ, v3 - v1 = r • (v2 - v1) := by
  have h21' : v2 - v1 ≠ 0 := sub_ne_zero.mpr h21
  -- The signed area equation rearranges to a chord-determinant identity.
  have hSA : (v2 0 - v1 0) * (v3 1 - v1 1) = (v3 0 - v1 0) * (v2 1 - v1 1) := by
    have := h
    unfold signedArea2 at this
    linarith
  -- Case split on whether the first coordinate of `v2 - v1` is nonzero.
  by_cases hx : v2 0 - v1 0 = 0
  · -- First coord zero, so second coord must be nonzero (else `v2 = v1`).
    have hy : v2 1 - v1 1 ≠ 0 := by
      intro hy0
      apply h21'
      ext i
      fin_cases i
      · change v2 0 - v1 0 = 0
        exact hx
      · change v2 1 - v1 1 = 0
        exact hy0
    -- From `hSA` and `hx`, deduce `v3 0 = v1 0`.
    have hx3 : v3 0 - v1 0 = 0 := by
      have hSA' : (v3 0 - v1 0) * (v2 1 - v1 1) = 0 := by
        rw [hx] at hSA
        linarith
      rcases mul_eq_zero.mp hSA' with h1 | h2
      · exact h1
      · exact (hy h2).elim
    refine ⟨(v3 1 - v1 1) / (v2 1 - v1 1), ?_⟩
    ext i
    fin_cases i
    · change (v3 - v1) 0 = (v3 1 - v1 1) / (v2 1 - v1 1) * (v2 - v1) 0
      have e1 : (v2 - v1) 0 = v2 0 - v1 0 := by simp
      have e2 : (v3 - v1) 0 = v3 0 - v1 0 := by simp
      rw [e1, e2, hx, hx3]
      simp
    · change (v3 - v1) 1 = (v3 1 - v1 1) / (v2 1 - v1 1) * (v2 - v1) 1
      have e1 : (v2 - v1) 1 = v2 1 - v1 1 := by simp
      have e2 : (v3 - v1) 1 = v3 1 - v1 1 := by simp
      rw [e1, e2]
      field_simp
  · -- First coord nonzero: use it as the "anchor" coordinate.
    refine ⟨(v3 0 - v1 0) / (v2 0 - v1 0), ?_⟩
    ext i
    fin_cases i
    · change (v3 - v1) 0 = (v3 0 - v1 0) / (v2 0 - v1 0) * (v2 - v1) 0
      have e1 : (v2 - v1) 0 = v2 0 - v1 0 := by simp
      have e2 : (v3 - v1) 0 = v3 0 - v1 0 := by simp
      rw [e1, e2]
      field_simp
    · change (v3 - v1) 1 = (v3 0 - v1 0) / (v2 0 - v1 0) * (v2 - v1) 1
      have e1 : (v2 - v1) 1 = v2 1 - v1 1 := by simp
      have e2 : (v3 - v1) 1 = v3 1 - v1 1 := by simp
      rw [e1, e2]
      field_simp
      linarith

end Erdos9796CountingFragment_Erdos9796Proof_P97_Moser_NonDeg
