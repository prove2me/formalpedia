-- Prove2me | solution 1 for Problem97.center_same_side_as_apex_of_nonobtuse
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:33.690172+00:00
-- url     : https://prove2.me/submissions/8d651da8-67b1-4fa5-b08d-24fe5c941a16

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CircumcenterSide:4197:6343. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.InnerProductSpace.Basic
import Theorems.Thm_Problem97_inner_chord_eq_two_mul_inner_midpoint
import Theorems.Thm_Problem97_signedArea_prod_eq_inner_mul_dist_sq

section Erdos9796CountingFragment_Erdos9796Proof_P97_CircumcenterSide

open Problem97

/- Fragment from Erdos9796Proof.P97.CircumcenterSide; source SHA-256 29ad9a32acf8129d66c4663579b3568047794eff971aa9120aac73db7971f861 -/


/-!
# Circumcenter-side characterization for non-obtuse inscribed triangles

Three points `a, b, c` on a Euclidean sphere of center `O` form a non-obtuse
triangle iff the smallest enclosing disk of `{a, b, c}` is the sphere itself.
Geometrically this puts the circumcenter `O` inside (or on the boundary of)
the triangle, which downstream consumers use through the signed-area form:
for each chord (say `ab`), the third vertex `c` and the center `O` lie on
the same closed half-plane.

The forward direction is captured by `center_same_side_as_apex_of_nonobtuse`:
if the interior angle of the triangle at `c` is non-obtuse — i.e.,
`⟪a - c, b - c⟫_ℝ ≥ 0` — then `signedArea2 O a b * signedArea2 c a b ≥ 0`.

The proof reduces to a single algebraic identity. With
`m := midpoint ℝ a b` and assuming the perpendicular-bisector condition
`‖a - O‖ = ‖b - O‖` (automatic from the sphere hypothesis):

  `signedArea2 O a b * signedArea2 c a b
      = ⟪m - O, m - c⟫_ℝ * ‖a - b‖²`.

The right-hand side is the product of a sphere-shaped quantity that the
inscribed-angle lemma `inner_chord_eq_two_mul_inner_midpoint` converts to
`(1/2) · ⟪a - c, b - c⟫_ℝ`, and a manifestly non-negative scalar `‖a - b‖²`.
Together with the hypothesis `⟪a - c, b - c⟫_ℝ ≥ 0`, this gives the result.

The companion `signedArea_prod_eq_inner_mul_dist_sq` is the abstract identity
without the inner-product hypothesis on `c`; it depends only on the
perpendicular-bisector condition on `O`. We also expose a `‖·‖²` form
(`signedArea_prod_eq_inner_mul_dist_sq`) that is more convenient for direct
algebraic chaining than re-deriving it from scratch.
-/

open scoped EuclideanGeometry InnerProductSpace






theorem solution
    {O a b c : ℝ²} {r : ℝ}
    (haO : ‖a - O‖ = r) (hbO : ‖b - O‖ = r) (hcO : ‖c - O‖ = r)
    (hacuteC : ⟪a - c, b - c⟫_ℝ ≥ 0) :
    signedArea2 O a b * signedArea2 c a b ≥ 0 := by
  -- Repackage the sphere conditions for the inscribed-angle lemma and
  -- the perp-bisector identity.
  have hac : ‖a - O‖ = ‖c - O‖ := by rw [haO, hcO]
  have hbc : ‖b - O‖ = ‖c - O‖ := by rw [hbO, hcO]
  have hab : ‖a - O‖ ^ 2 = ‖b - O‖ ^ 2 := by rw [haO, hbO]
  -- Inscribed-angle identity: `⟪a-c, b-c⟫ = 2 · ⟪m - O, m - c⟫`.
  have hchord := inner_chord_eq_two_mul_inner_midpoint hac hbc
  -- Hence the midpoint-centered inner product is non-negative.
  have hmid_nn : ⟪midpoint ℝ a b - O, midpoint ℝ a b - c⟫_ℝ ≥ 0 := by
    linarith [hchord]
  -- Apply the signed-area product identity and multiply.
  rw [signedArea_prod_eq_inner_mul_dist_sq O a b c hab]
  exact mul_nonneg hmid_nn (sq_nonneg _)

end Erdos9796CountingFragment_Erdos9796Proof_P97_CircumcenterSide
