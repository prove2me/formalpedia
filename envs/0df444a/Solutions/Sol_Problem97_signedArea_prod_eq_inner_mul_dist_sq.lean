-- Prove2me | solution 1 for Problem97.signedArea_prod_eq_inner_mul_dist_sq
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:05:56.06172+00:00
-- url     : https://prove2.me/submissions/ec01eac8-6310-4c37-b8e4-2ec7faad7bb3

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CircumcenterSide:1889:4195. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.InnerProductSpace.Basic

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
    (O a b c : ℝ²)
    (hperp : ‖a - O‖ ^ 2 = ‖b - O‖ ^ 2) :
    signedArea2 O a b * signedArea2 c a b =
      ⟪midpoint ℝ a b - O, midpoint ℝ a b - c⟫_ℝ * ‖a - b‖ ^ 2 := by
  -- Expand the perp-bisector hypothesis into coordinate form.
  have hperp_coord :
      (a 0 - O 0) ^ 2 + (a 1 - O 1) ^ 2 =
        (b 0 - O 0) ^ 2 + (b 1 - O 1) ^ 2 := by
    have h := hperp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h
    simpa [Fin.sum_univ_two] using h
  -- Coordinate form for the midpoint.
  have hmid0 : (midpoint ℝ a b) 0 = (a 0 + b 0) / 2 := by
    rw [midpoint_eq_smul_add]; simp; ring
  have hmid1 : (midpoint ℝ a b) 1 = (a 1 + b 1) / 2 := by
    rw [midpoint_eq_smul_add]; simp; ring
  -- Coordinate form for the midpoint-centered inner product.
  have hinner :
      ⟪midpoint ℝ a b - O, midpoint ℝ a b - c⟫_ℝ =
        ((a 0 + b 0) / 2 - O 0) * ((a 0 + b 0) / 2 - c 0) +
        ((a 1 + b 1) / 2 - O 1) * ((a 1 + b 1) / 2 - c 1) := by
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_two, PiLp.sub_apply, hmid0, hmid1]
    ring
  -- Coordinate form for the squared chord length.
  have hnsq : ‖a - b‖ ^ 2 = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two]
  rw [signedArea2, signedArea2, hinner, hnsq]
  -- The perp-bisector hypothesis becomes `⟪a - b, m - O⟫ = 0` in coordinates.
  have key :
      (a 0 - b 0) * ((a 0 + b 0) / 2 - O 0) +
      (a 1 - b 1) * ((a 1 + b 1) / 2 - O 1) = 0 := by
    nlinarith [hperp_coord]
  -- A `linear_combination` witness wraps up the quartic identity.
  linear_combination
    -((a 0 - b 0) * ((a 0 + b 0) / 2 - c 0) +
      (a 1 - b 1) * ((a 1 + b 1) / 2 - c 1)) * key

end Erdos9796CountingFragment_Erdos9796Proof_P97_CircumcenterSide
