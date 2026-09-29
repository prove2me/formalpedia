-- Prove2me | solution 1 for Problem97.MEC.not_collinear_of_three_dist_eq
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:25.967708+00:00
-- url     : https://prove2.me/submissions/a9ed0d40-0626-4c37-8c9c-c805be8695b9

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.Moser.NonDeg:5479:6818. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation

section Erdos9796CountingFragment_Erdos9796Proof_P97_Moser_NonDeg

open Problem97 Problem97.MEC

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










theorem solution {p₁ p₂ p₃ c : ℝ²} {r : ℝ}
    (h1 : dist p₁ c = r) (h2 : dist p₂ c = r) (h3 : dist p₃ c = r)
    (h12 : p₁ ≠ p₂) (h23 : p₂ ≠ p₃) (h13 : p₁ ≠ p₃) :
    ¬ Collinear ℝ ({p₁, p₂, p₃} : Set ℝ²) := by
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
  · -- `Wbtw p₁ p₂ p₃` with `p₂ ≠ p₁` and `p₂ ≠ p₃` gives `Sbtw p₁ p₂ p₃`.
    have hs : Sbtw ℝ p₁ p₂ p₃ := ⟨hw, h12.symm, h23⟩
    have hd := hs.dist_lt_max_dist c
    rw [h1, h3, max_self] at hd
    linarith [h2]
  · have hs : Sbtw ℝ p₂ p₃ p₁ := ⟨hw, h23.symm, h13.symm⟩
    have hd := hs.dist_lt_max_dist c
    rw [h1, h2, max_self] at hd
    linarith [h3]
  · have hs : Sbtw ℝ p₃ p₁ p₂ := ⟨hw, h13, h12⟩
    have hd := hs.dist_lt_max_dist c
    rw [h2, h3, max_self] at hd
    linarith [h1]

end Erdos9796CountingFragment_Erdos9796Proof_P97_Moser_NonDeg
