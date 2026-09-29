-- Prove2me | solution 1 for Problem97.MEC.exists_nonobtuse_circumscribed_triple
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:51.935279+00:00
-- url     : https://prove2.me/submissions/a1666c2e-0f88-4923-a3e0-5289ac950805

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.Moser.TriangleNonObtuse:23745:33035. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Definitions.Def_Erdos9796Counting_MEC_Boundary
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Theorems.Thm_Problem97_MEC_mec_center_mem_convexHull_boundary
import Theorems.Thm_Problem97_inner_chord_eq_two_mul_inner_midpoint
import Theorems.Thm_Problem97_signedArea_prod_eq_inner_mul_dist_sq

section Erdos9796CountingFragment_Erdos9796Proof_P97_MEC_Boundary

open Problem97 Problem97.MEC

/- Fragment from Erdos9796Proof.P97.MEC.Boundary; source SHA-256 e7d16b0637be4dd967cade4cfb9db7d4ba52c8fdb229ece7b87498ff207e21a7 -/


/-!
# MEC boundary structure — Sylvester (1857) dichotomy

For any nonempty noncollinear finite point set `A ⊆ ℝ²` we prove the
classical Sylvester dichotomy on the minimum enclosing circle (MEC) of
`A`:

* **Diameter case** — two points of `A` lie diametrically opposite on
  the MEC boundary, pinning the centre to their midpoint, OR
* **Circumscribed case** — at least three points of `A` lie on the MEC
  boundary.

The naive "≥3 boundary points" statement is **false** in general:
obtuse triangles realise the diameter case (the two acute-angle vertices
form an antipodal pair on the MEC, the obtuse vertex sits strictly
inside).  The disjunction below is the correct formulation, due to
Sylvester (1857).

The argument is variational.  Define
`B(A) := { p ∈ A | dist p M.center = M.radius }`, the set of points
realising the maximum distance from the MEC centre.  Then:

* `B.card = 0` is impossible: by continuity of `radF`, every point sits
  strictly inside, so we can shrink `M.radius` keeping the centre fixed
  — contradicting minimality.
* `B.card = 1` is impossible for noncollinear `A`: perturb the centre
  toward the lone boundary point.  Strict interior distance to other
  points is preserved by continuity, so we obtain a smaller enclosing
  radius — contradicting minimality.
* `B.card = 2` forces the diameter case: the two boundary points
  `p, q` pin the centre to their midpoint (otherwise we could shift
  along the perpendicular bisector toward `midpoint p q` to shrink the
  radius — same contradiction).
* `B.card ≥ 3` is the circumscribed case by definition.

The core perturbation uses an algebraic identity: along the segment
from `c := M.center` toward a target `q*` chosen so that
`⟨p - c, q* - c⟩ = ‖q* - c‖²` for every boundary point `p ∈ B`,
the squared distance `‖p - c'(t)‖²` equals
`M.radius² + (t² - 2t) ‖q* - c‖²`, which is strictly less than
`M.radius²` for `t ∈ (0, 2)` (and `q* ≠ c`).  For interior points the
distance change is bounded by `t · ‖q* - c‖`, so picking `t` small
enough keeps them inside as well.

## Main theorem

* `Problem97.MEC.sylvester_dichotomy` — the Sylvester (1857) dichotomy
  in disjunctive form, suitable for downstream consumers branching on
  the two cases.
-/

open scoped EuclideanGeometry
open Finset




/- ### Boundary set of the MEC -/



/-- Membership in the MEC boundary is membership in `A` together with
equality to the radius from the MEC centre. -/
lemma Problem97.MEC.mem_boundary_iff {A : Finset ℝ²} (hA : A.Nonempty) {p : ℝ²} :
    p ∈ boundary A hA ↔ p ∈ A ∧ dist p (mec A hA).center = (mec A hA).radius := by
  classical
  simp [boundary]



/- ### Auxiliary helpers -/









/- ### Boundary card lower bound: ≥ 1 -/



/- ### Sentinel computation: distance along a "shrink-toward-target" line.

We isolate the algebraic identity that underlies both the card-1 and card-2
variational arguments.  If `p, c, q* : ℝ²` satisfy
`⟨p - c, q* - c⟩ = ‖q* - c‖²`, then
`‖p - (c + t • (q* - c))‖² = ‖p - c‖² - (2t - t²) ‖q* - c‖²`.

For `card = 1` with single boundary point `p₀`, take `q* := p₀`; then
`⟨p₀ - c, p₀ - c⟩ = ‖p₀ - c‖² = M.radius² = ‖q* - c‖²` (uses `q* - c = p₀ - c`).

For `card = 2` with boundary `{p, q}`, take `q* := midpoint p q = m`; then
on the perpendicular bisector, `⟨p - c, m - c⟩ = ‖m - c‖²`.
-/





/- ### Card 1 case — impossible for noncollinear A -/



/- ### Card 2 case — diameter case -/









/- ### Main theorem -/

end Erdos9796CountingFragment_Erdos9796Proof_P97_MEC_Boundary

section Erdos9796CountingFragment_Erdos9796Proof_P97_Moser_TriangleNonObtuse

open Problem97 Problem97.MEC

/- Fragment from Erdos9796Proof.P97.Moser.TriangleNonObtuse; source SHA-256 2a8d00cd1d6b2290156c6085675919cde734d3890ca0877876d719ff756a7348 -/


/-!
# Non-obtuse Moser triangle in the circumscribed branch

In the **circumscribed branch** of the Sylvester (1857) dichotomy
(`Problem97.MEC.sylvester_dichotomy`), at least three points of `A` lie on the
MEC boundary.  This file extracts a *non-obtuse* such triple: three distinct
boundary points `a, b, c` of `A` whose triangle has all three vertex angles
at most `π / 2`, equivalently

  `⟪b - a, c - a⟫_ℝ ≥ 0`, `⟪c - b, a - b⟫_ℝ ≥ 0`, `⟪a - c, b - c⟫_ℝ ≥ 0`.

The proof route is Carathéodory in dimension 2.  Let
`B := { p ∈ A | dist p O = r }` be the MEC boundary realisers
(`O = (mec A hA).center`, `r = (mec A hA).radius`).

* **Welzl invariant.**  `O ∈ convexHull ℝ (B : Set ℝ²)`.  Otherwise the
  closed-convex projection of `O` onto `convexHull ℝ B` gives a separating
  direction `v - O` with `⟪p - O, v - O⟫ ≥ ‖v - O‖² > 0` for every `p ∈ B`.
  Translating the centre by a small multiple of `v - O` strictly decreases
  the enclosing radius, contradicting MEC minimality.
* **Carathéodory in dim 2.**  Apply `Caratheodory.minCardFinsetOfMemConvexHull`
  to `O ∈ conv B`: there is an affinely independent `T ⊆ B` with
  `O ∈ convexHull ℝ T`.  Affine independence in `ℝ²` caps `T.card ≤ 3`.
* **Case split on `T.card`.**
  * `card = 1`: `O ∈ {p} ⊆ B` would force `dist p O = 0 = r`, but `r > 0` for
    noncollinear `A`.  Contradiction.
  * `card = 2`: `T = {p, q}`, `O` on segment `[p, q]`.  Boundary equidistance
    + segment membership forces `O = midpoint p q` with `dist p q = 2 r` —
    the diameter configuration.  Pick any third boundary point
    `c ∈ B \ {p, q}` (available by the hypothesis `3 ≤ B.card`).  The right
    angle at `c` (Thales) plus the acute angles at `p, q` give the three
    inner-product inequalities.
  * `card = 3`: `T = {a, b, c}` distinct.  `O ∈ conv {a, b, c}` rewrites as
    a barycentric combination `O = α • a + β • b + γ • c`; the algebraic
    identity `signedArea2 O a b * signedArea2 c a b = γ · signedArea2 c a b²`
    gives the "same-side" condition for each chord, which converts to the
    inner-product nonnegativity via
    `Problem97.signedArea_prod_eq_inner_mul_dist_sq` (forward direction).

## Main results

* `Problem97.MEC.mec_center_mem_convexHull_boundary` — Welzl invariant.
* `Problem97.MEC.exists_nonobtuse_circumscribed_triple` — extraction of the
  non-obtuse boundary triple.
* `Problem97.MEC.nonobtuseCircumscribedMoserTriangle` — packaging into
  the existing `MoserTriangle` structure.
* `Problem97.MEC.nonobtuseCircumscribedMoserTriangle_nonobtuse` — the three
  inner-product nonnegativity inequalities for the packaged triangle.
-/

open scoped EuclideanGeometry InnerProductSpace
open Finset




/- ### Auxiliary: shrink-along-direction identity and small numerical lemmas. -/





/- ### MEC boundary set -/

-- Reuse MEC boundary lemmas from `MEC.Boundary` for a single canonical source
-- of `boundary`, `boundary_nonempty`, `mem_boundary_iff`, and `mec_radius_pos`.

/- ### Sub-lemma X: Welzl invariant -/



/- ### Diameter (Thales) auxiliaries -/

/-- **Thales' theorem (algebraic).**  If `p, q, c` are on a sphere of centre
`O` (radius `r > 0`) and `O = midpoint p q`, then the angle at `c`
subtending `pq` is exactly right: `⟪p - c, q - c⟫_ℝ = 0`. -/
 lemma Problem97.MEC.diameter_thales_inner_zero
    {O p q c : ℝ²} {r : ℝ}
    (hpO : ‖p - O‖ = r) (hqO : ‖q - O‖ = r) (hcO : ‖c - O‖ = r)
    (hO : O = midpoint ℝ p q) :
    ⟪p - c, q - c⟫_ℝ = 0 := by
  have hpc : ‖p - O‖ = ‖c - O‖ := by rw [hpO, hcO]
  have hqc : ‖q - O‖ = ‖c - O‖ := by rw [hqO, hcO]
  have hchord := Problem97.inner_chord_eq_two_mul_inner_midpoint hpc hqc
  -- midpoint p q - O = 0 since O = midpoint p q.
  have hmid_O : midpoint ℝ p q - O = 0 := by rw [hO]; abel
  rw [hchord, hmid_O, inner_zero_left, mul_zero]

/-- **Algebraic side-inner-product identity.**  For any four points,
`⟪q - p, c - p⟫_ℝ + ⟪p - c, q - c⟫_ℝ = ‖c - p‖²`.  Specialised to the
diameter configuration `O = midpoint p q` (where the second term vanishes),
this gives `⟪q - p, c - p⟫_ℝ = ‖c - p‖² ≥ 0`. -/
 lemma Problem97.MEC.diameter_inner_side_nonneg (p q c : ℝ²) :
    ⟪q - p, c - p⟫_ℝ = ‖c - p‖ ^ 2 - ⟪p - c, q - c⟫_ℝ := by
  have hkey : ⟪q - p, c - p⟫_ℝ + ⟪p - c, q - c⟫_ℝ = ‖c - p‖ ^ 2 := by
    -- (q - p) = (q - c) - (p - c).
    -- (c - p) = -(p - c).  So ⟪q - p, c - p⟫ = -⟪q - p, p - c⟫.
    -- ⟪q - p, p - c⟫ = ⟪q - c, p - c⟫ - ⟪p - c, p - c⟫
    --                = ⟪q - c, p - c⟫ - ‖p - c‖².
    -- And ⟪p - c, q - c⟫ = ⟪p - c, q - c⟫ (by symmetry of inner product).
    have h1 : q - p = (q - c) - (p - c) := by abel
    have h2 : c - p = -(p - c) := by abel
    rw [h1, h2, inner_neg_right, inner_sub_left]
    rw [show ⟪p - c, q - c⟫_ℝ = ⟪q - c, p - c⟫_ℝ from real_inner_comm _ _]
    rw [real_inner_self_eq_norm_sq]
    rw [norm_neg]; ring
  linarith [hkey]

/-- Bound from Cauchy–Schwarz on the on-sphere chord inner product: with
`‖p - O‖ = ‖c - O‖ = r`, `|⟪p - c, q - c⟫_ℝ| ≤ ‖p - c‖ · ‖q - c‖`. -/
 lemma Problem97.MEC.diameter_inner_pq_le_normSq
    {O p q c : ℝ²} {r : ℝ}
    (hpO : ‖p - O‖ = r) (hqO : ‖q - O‖ = r) (hcO : ‖c - O‖ = r)
    (hO : O = midpoint ℝ p q) :
    ⟪p - c, q - c⟫_ℝ = 0 ∧
    ⟪q - p, c - p⟫_ℝ = ‖c - p‖ ^ 2 ∧
    ⟪p - q, c - q⟫_ℝ = ‖c - q‖ ^ 2 := by
  have hth := Problem97.MEC.diameter_thales_inner_zero hpO hqO hcO hO
  refine ⟨hth, ?_, ?_⟩
  · have heq := Problem97.MEC.diameter_inner_side_nonneg p q c
    linarith
  · -- Swap p and q in `diameter_inner_side_nonneg`.
    have heq := Problem97.MEC.diameter_inner_side_nonneg q p c
    have hsymm : ⟪q - c, p - c⟫_ℝ = ⟪p - c, q - c⟫_ℝ := real_inner_comm _ _
    linarith

/- ### Barycentric (card 3) case -/

/-- Coordinate-by-coordinate expansion of a 2D affine combination. -/
 lemma Problem97.MEC.euclideanSpace_affineComb_apply (a b c : ℝ²) (α β γ : ℝ) (i : Fin 2) :
    (α • a + β • b + γ • c) i = α * a i + β * b i + γ * c i := by
  simp [PiLp.add_apply, PiLp.smul_apply]

/-- Barycentric expansion of the signed area, with `a, b` as the chord:
`signedArea2 (αa + βb + γc) a b = γ · signedArea2 c a b` (using `α + β + γ = 1`). -/
 lemma Problem97.MEC.signedArea2_baryComb_eq
    (a b c : ℝ²) (α β γ : ℝ) (hsum : α + β + γ = 1) :
    Problem97.signedArea2 (α • a + β • b + γ • c) a b
      = γ * Problem97.signedArea2 c a b := by
  unfold Problem97.signedArea2
  rw [Problem97.MEC.euclideanSpace_affineComb_apply, Problem97.MEC.euclideanSpace_affineComb_apply]
  have habg : α = 1 - β - γ := by linarith
  rw [habg]; ring

/-- Barycentric "same-side" of `O = αa + βb + γc` and `c` over chord `ab`,
when `α, β, γ ≥ 0` and sum 1:
`signedArea2 O a b * signedArea2 c a b = γ · signedArea2 c a b² ≥ 0`. -/
 lemma Problem97.MEC.signedArea_prod_baryComb_nonneg
    (a b c : ℝ²) {α β γ : ℝ} (_hα : 0 ≤ α) (_hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hsum : α + β + γ = 1) :
    0 ≤ Problem97.signedArea2 (α • a + β • b + γ • c) a b *
        Problem97.signedArea2 c a b := by
  rw [Problem97.MEC.signedArea2_baryComb_eq a b c α β γ hsum]
  -- γ * (signedArea2 c a b) * (signedArea2 c a b) = γ * (signedArea2 c a b)²
  have hsq : Problem97.signedArea2 c a b * Problem97.signedArea2 c a b
            = Problem97.signedArea2 c a b ^ 2 := by ring
  have hsq_nn : 0 ≤ Problem97.signedArea2 c a b ^ 2 := sq_nonneg _
  have := mul_nonneg hγ hsq_nn
  -- γ * (sa c a b)² = γ * sa c a b * sa c a b
  nlinarith [this]

/-- **Non-obtuse-at-`c` from O in barycentric hull.**  If
`a, b, c` lie on a sphere of centre `O` and radius `r`, `a ≠ b`, and
`O = α • a + β • b + γ • c` with `α, β, γ ≥ 0` and sum 1, then the
inner product `⟪a - c, b - c⟫_ℝ` is nonnegative — equivalently, the angle
at `c` is non-obtuse. -/
 lemma Problem97.MEC.inner_chord_nonneg_of_baryComb
    {a b c O : ℝ²}
    (haO : ‖a - O‖ = ‖c - O‖) (hbO : ‖b - O‖ = ‖c - O‖)
    (hab : a ≠ b)
    {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hsum : α + β + γ = 1) (hO : O = α • a + β • b + γ • c) :
    0 ≤ ⟪a - c, b - c⟫_ℝ := by
  -- Step 1: `signedArea_prod_eq_inner_mul_dist_sq` gives the key identity.
  have hperp : ‖a - O‖ ^ 2 = ‖b - O‖ ^ 2 := by rw [haO, hbO]
  have h1 := Problem97.signedArea_prod_eq_inner_mul_dist_sq O a b c hperp
  -- h1 : signedArea2 O a b * signedArea2 c a b = ⟪m - O, m - c⟫ * ‖a - b‖²
  -- Step 2: rewrite `signedArea2 O a b * signedArea2 c a b ≥ 0` from barycentric.
  have h2 : 0 ≤ Problem97.signedArea2 O a b * Problem97.signedArea2 c a b := by
    rw [hO]; exact Problem97.MEC.signedArea_prod_baryComb_nonneg a b c hα hβ hγ hsum
  -- Step 3: combine to get `⟪m - O, m - c⟫ * ‖a - b‖² ≥ 0`.
  have h3 : 0 ≤ ⟪midpoint ℝ a b - O, midpoint ℝ a b - c⟫_ℝ * ‖a - b‖ ^ 2 := by
    rw [← h1]; exact h2
  -- Step 4: since ‖a - b‖² > 0, get `⟪m - O, m - c⟫ ≥ 0`.
  have hab_sq_pos : 0 < ‖a - b‖ ^ 2 := by
    have : ‖a - b‖ > 0 := norm_sub_pos_iff.mpr hab
    positivity
  have h4 : 0 ≤ ⟪midpoint ℝ a b - O, midpoint ℝ a b - c⟫_ℝ := by
    by_contra hneg
    push_neg at hneg
    have : ⟪midpoint ℝ a b - O, midpoint ℝ a b - c⟫_ℝ * ‖a - b‖ ^ 2 < 0 :=
      mul_neg_of_neg_of_pos hneg hab_sq_pos
    linarith
  -- Step 5: inscribed-angle identity `⟪a - c, b - c⟫ = 2 · ⟪m - O, m - c⟫`.
  have h5 := Problem97.inner_chord_eq_two_mul_inner_midpoint haO hbO
  linarith

/-- From `O ∈ segment p q` and `dist p O = dist q O = r`, with `p ≠ q`,
deduce that `O = midpoint p q` (and `dist p q = 2 r`).  This is the
"segment-membership ⇒ diameter configuration" lemma. -/
 lemma Problem97.MEC.diameter_of_segment_equidist
    {p q O : ℝ²} {r : ℝ} (hpq : p ≠ q)
    (hpO : dist p O = r) (hqO : dist q O = r)
    (hO : O ∈ segment ℝ p q) :
    O = midpoint ℝ p q ∧ dist p q = 2 * r := by
  obtain ⟨α, β, hα, hβ, hsum, heq⟩ := hO
  have hOp : O - p = β • (q - p) := by
    rw [← heq]
    have hα_eq : α = 1 - β := by linarith
    rw [hα_eq]; module
  have hOq : O - q = α • (p - q) := by
    rw [← heq]
    have hβ_eq : β = 1 - α := by linarith
    rw [hβ_eq]; module
  have hqp_pq : ‖q - p‖ = ‖p - q‖ := by
    rw [show q - p = -(p - q) from by abel, norm_neg]
  have h1 : dist p O = β * dist p q := by
    rw [dist_eq_norm, show p - O = -(O - p) from by abel, norm_neg, hOp,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ, dist_eq_norm, hqp_pq]
  have h2 : dist q O = α * dist p q := by
    rw [dist_eq_norm, show q - O = -(O - q) from by abel, norm_neg, hOq,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hα, dist_eq_norm]
  have hd_pos : 0 < dist p q := dist_pos.mpr hpq
  rw [hpO] at h1; rw [hqO] at h2
  have hαβ_eq : α = β := by
    have key : (α - β) * dist p q = 0 := by
      have hαd : α * dist p q = r := h2.symm
      have hβd : β * dist p q = r := h1.symm
      nlinarith
    have hd_ne : dist p q ≠ 0 := ne_of_gt hd_pos
    rcases mul_eq_zero.mp key with hαβ | hd0
    · linarith
    · exact absurd hd0 hd_ne
  have hα_eq : α = 1/2 := by linarith
  have hβ_eq : β = 1/2 := by linarith
  have hd_eq : dist p q = 2 * r := by
    have hβd : β * dist p q = r := h1.symm
    rw [hβ_eq] at hβd; linarith
  refine ⟨?_, hd_eq⟩
  rw [← heq, hα_eq, hβ_eq, midpoint_eq_smul_add]
  have h12 : (⅟2 : ℝ) = 1/2 := by simp [invOf_eq_inv]
  rw [h12]; module

/- ### Carathéodory cardinality bound in dim 2 -/

/-- For any `x ∈ convexHull ℝ s` in `ℝ²`, the Carathéodory `minCardFinset`
has cardinality at most 3. -/
 lemma Problem97.MEC.minCardFinset_card_le_three
    {s : Set ℝ²} {x : ℝ²} (hx : x ∈ convexHull ℝ s) :
    (Caratheodory.minCardFinsetOfMemConvexHull hx).card ≤ 3 := by
  set T := Caratheodory.minCardFinsetOfMemConvexHull hx
  have haff : AffineIndependent ℝ (Subtype.val : (↑T : Set ℝ²) → ℝ²) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have hcard := haff.card_le_finrank_succ
  have h_fc_eq : Fintype.card ((↑T : Set ℝ²) : Type) = T.card := by
    simp [Fintype.card_coe]
  have h_finrank_le : Module.finrank ℝ
      (vectorSpan ℝ (Set.range (Subtype.val : (↑T : Set ℝ²) → ℝ²))) ≤ 2 := by
    have := Submodule.finrank_le (vectorSpan ℝ
      (Set.range (Subtype.val : (↑T : Set ℝ²) → ℝ²)))
    rw [finrank_euclideanSpace_fin] at this
    exact this
  have h1 : Fintype.card ((↑T : Set ℝ²) : Type) ≤ 3 := by linarith
  rw [h_fc_eq] at h1
  exact h1

/- ### Conversion of `convexHull` of small Finsets to explicit barycentric form -/

/-- Convex-hull membership for a `Finset` of three distinct points, in
barycentric form. -/
 lemma Problem97.MEC.mem_convexHull_three
    {a b c x : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hx : x ∈ convexHull ℝ ((({a, b, c} : Finset ℝ²) : Set ℝ²))) :
    ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
      α • a + β • b + γ • c = x := by
  classical
  rw [Finset.mem_convexHull] at hx
  obtain ⟨w, hw_nn, hw_sum, hcm⟩ := hx
  have hT_eq : ({a, b, c} : Finset ℝ²) =
      insert a (insert b ({c} : Finset ℝ²)) := rfl
  have hsum_eq : ∑ y ∈ ({a, b, c} : Finset _), w y = w a + w b + w c := by
    rw [hT_eq]
    rw [Finset.sum_insert (by simp [hab, hac])]
    rw [Finset.sum_insert (by simp [hbc])]
    simp; ring
  refine ⟨w a, w b, w c, ?_, ?_, ?_, ?_, ?_⟩
  · exact hw_nn a (by simp)
  · exact hw_nn b (by simp)
  · exact hw_nn c (by simp)
  · linarith [hw_sum, hsum_eq]
  · unfold Finset.centerMass at hcm
    rw [hw_sum, inv_one, one_smul] at hcm
    rw [hT_eq] at hcm
    rw [Finset.sum_insert (by simp [hab, hac])] at hcm
    rw [Finset.sum_insert (by simp [hbc])] at hcm
    simp only [Finset.sum_singleton, id] at hcm
    rw [← hcm]; abel

/-- Convex-hull membership for a `Finset` of two distinct points: an explicit
point on the segment. -/
 lemma Problem97.MEC.mem_convexHull_two
    {p q x : ℝ²} (_hpq : p ≠ q)
    (hx : x ∈ convexHull ℝ ((({p, q} : Finset ℝ²) : Set ℝ²))) :
    x ∈ segment ℝ p q := by
  classical
  -- {p, q} as a Finset has the same coe as a Set, and convexHull pair = segment.
  have heq : (({p, q} : Finset ℝ²) : Set ℝ²) = ({p, q} : Set ℝ²) := by
    ext; simp
  rw [heq, convexHull_pair] at hx
  exact hx

/-- Convex-hull membership for a singleton `Finset`: forces equality. -/
 lemma Problem97.MEC.mem_convexHull_one {p x : ℝ²}
    (hx : x ∈ convexHull ℝ ((({p} : Finset ℝ²) : Set ℝ²))) : x = p := by
  have heq : (({p} : Finset ℝ²) : Set ℝ²) = ({p} : Set ℝ²) := by ext; simp
  rw [heq, convexHull_singleton, Set.mem_singleton_iff] at hx
  exact hx

/- ### Main extraction theorem -/


theorem solution
    {A : Finset ℝ²} (hA : A.Nonempty) (hncol : ¬ Collinear ℝ (A : Set ℝ²))
    (hcirc : 3 ≤ (A.filter
      (fun p => dist p (mec A hA).center = (mec A hA).radius)).card) :
    ∃ a b c : ℝ², a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      dist a (mec A hA).center = (mec A hA).radius ∧
      dist b (mec A hA).center = (mec A hA).radius ∧
      dist c (mec A hA).center = (mec A hA).radius ∧
      ⟪b - a, c - a⟫_ℝ ≥ 0 ∧
      ⟪c - b, a - b⟫_ℝ ≥ 0 ∧
      ⟪a - c, b - c⟫_ℝ ≥ 0 := by
  classical
  set M := mec A hA with hM_def
  set B := boundary A hA with hB_def
  have hB_eq : B = A.filter (fun p => dist p M.center = M.radius) := rfl
  -- B.card ≥ 3 from the hypothesis.
  have hB_card : 3 ≤ B.card := hcirc
  have hr_pos : 0 < M.radius := mec_radius_pos hA hncol
  -- Welzl invariant: O ∈ conv B.
  have hO_in_conv : M.center ∈ convexHull ℝ ((B : Set ℝ²)) :=
    mec_center_mem_convexHull_boundary hA hncol
  -- Carathéodory: produce T ⊆ B with `T.card ≤ 3`, T affine-independent,
  -- O ∈ conv ↑T.  Combined with sub-lemma X.
  set T := Caratheodory.minCardFinsetOfMemConvexHull hO_in_conv with hT_def
  have hT_ne : T.Nonempty := Caratheodory.minCardFinsetOfMemConvexHull_nonempty _
  have hT_sub : (T : Set ℝ²) ⊆ (B : Set ℝ²) :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq _
  have hO_in_T : M.center ∈ convexHull ℝ (T : Set ℝ²) :=
    Caratheodory.mem_minCardFinsetOfMemConvexHull _
  have hT_card : T.card ≤ 3 := Problem97.MEC.minCardFinset_card_le_three _
  -- Membership helper: anything in T inherits the boundary properties.
  have hT_mem_B : ∀ p ∈ T, p ∈ B := fun p hp => hT_sub hp
  have hT_mem_data : ∀ p ∈ T, p ∈ A ∧ dist p M.center = M.radius :=
    fun p hp => (mem_boundary_iff hA).1 (hT_mem_B p hp)
  -- Casing on T.card ∈ {1, 2, 3}.
  have hT_card_pos : 1 ≤ T.card := T.card_pos.mpr hT_ne
  have hT_card_eq : T.card = 1 ∨ T.card = 2 ∨ T.card = 3 := by omega
  rcases hT_card_eq with hT1 | hT2 | hT3
  · -- card = 1: T = {p}, O ∈ {p} ⟹ O = p, but dist p O = r > 0.
    rw [Finset.card_eq_one] at hT1
    obtain ⟨p, hp⟩ := hT1
    have hp_in : p ∈ T := by rw [hp]; exact Finset.mem_singleton_self _
    have hp_dist : dist p M.center = M.radius := (hT_mem_data p hp_in).2
    have hp_eq_O : M.center = p := by
      have hO' : M.center ∈ convexHull ℝ ((T : Finset ℝ²) : Set ℝ²) := hO_in_T
      rw [hp] at hO'
      have := Problem97.MEC.mem_convexHull_one hO'
      exact this
    -- Contradiction: dist p p = 0 ≠ r.
    exfalso
    rw [← hp_eq_O, dist_self] at hp_dist
    linarith
  · -- card = 2: T = {p, q} distinct.  Diameter configuration.
    rw [Finset.card_eq_two] at hT2
    obtain ⟨p, q, hpq, hpqT⟩ := hT2
    have hp_in : p ∈ T := by rw [hpqT]; exact Finset.mem_insert_self _ _
    have hq_in : q ∈ T := by
      rw [hpqT]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hp_data := hT_mem_data p hp_in
    have hq_data := hT_mem_data q hq_in
    have hp_mem : p ∈ A := hp_data.1
    have hq_mem : q ∈ A := hq_data.1
    have hp_dist : dist p M.center = M.radius := hp_data.2
    have hq_dist : dist q M.center = M.radius := hq_data.2
    -- O ∈ conv ↑T = conv {p, q} = segment p q.
    have hO_seg : M.center ∈ segment ℝ p q := by
      have hO' : M.center ∈ convexHull ℝ ((T : Finset ℝ²) : Set ℝ²) := hO_in_T
      rw [hpqT] at hO'
      exact Problem97.MEC.mem_convexHull_two hpq hO'
    -- Diameter configuration: O = midpoint p q, dist p q = 2r.
    obtain ⟨hO_mid, hd_eq⟩ :=
      Problem97.MEC.diameter_of_segment_equidist hpq hp_dist hq_dist hO_seg
    -- Now extract a third boundary point c ∈ B \ {p, q}.
    have hpq_sub_B : ({p, q} : Finset ℝ²) ⊆ B := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hxp | hxq
      · rw [hxp]; exact hT_mem_B p hp_in
      · rw [Finset.mem_singleton] at hxq; rw [hxq]; exact hT_mem_B q hq_in
    have hpq_card : ({p, q} : Finset ℝ²).card = 2 :=
      Finset.card_pair hpq
    have hex_c : ∃ c ∈ B, c ∉ ({p, q} : Finset ℝ²) := by
      by_contra hno
      push_neg at hno
      have hB_sub : B ⊆ ({p, q} : Finset ℝ²) := by
        intro c hc
        by_contra hcno
        exact hcno (hno c hc)
      -- Contradiction: B.card ≤ ({p,q}).card = 2, but hB_card says ≥ 3.
      have : B.card ≤ 2 := by
        calc B.card ≤ ({p, q} : Finset ℝ²).card := Finset.card_le_card hB_sub
          _ = 2 := hpq_card
      linarith
    obtain ⟨c, hc_B, hc_not⟩ := hex_c
    have hc_data := (mem_boundary_iff hA).1 hc_B
    have hc_mem : c ∈ A := hc_data.1
    have hc_dist : dist c M.center = M.radius := hc_data.2
    have hcp : c ≠ p := by
      intro h; apply hc_not; rw [h]; exact Finset.mem_insert_self _ _
    have hcq : c ≠ q := by
      intro h; apply hc_not; rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    -- Now apply diameter inner-product bounds.
    have hpO_norm : ‖p - M.center‖ = M.radius := by rw [← dist_eq_norm]; exact hp_dist
    have hqO_norm : ‖q - M.center‖ = M.radius := by rw [← dist_eq_norm]; exact hq_dist
    have hcO_norm : ‖c - M.center‖ = M.radius := by rw [← dist_eq_norm]; exact hc_dist
    have ⟨hth, hsp, hsq⟩ :=
      Problem97.MEC.diameter_inner_pq_le_normSq hpO_norm hqO_norm hcO_norm hO_mid
    -- Use (a, b, c) := (p, q, c).
    refine ⟨p, q, c, hp_mem, hq_mem, hc_mem, hpq, fun h => hcq h.symm,
      fun h => hcp h.symm, hp_dist, hq_dist, hc_dist, ?_, ?_, ?_⟩
    · -- ⟪q - p, c - p⟫ ≥ 0
      rw [hsp]; positivity
    · -- ⟪c - q, p - q⟫ ≥ 0
      rw [show ⟪c - q, p - q⟫_ℝ = ⟪p - q, c - q⟫_ℝ from real_inner_comm _ _, hsq]
      positivity
    · -- ⟪p - c, q - c⟫ = 0
      rw [hth]
  · -- card = 3: T = {a, b, c} distinct, affinely independent.
    rw [Finset.card_eq_three] at hT3
    obtain ⟨a, b, c, hab, hac, hbc, hTeq⟩ := hT3
    have ha_in : a ∈ T := by rw [hTeq]; simp
    have hb_in : b ∈ T := by rw [hTeq]; simp
    have hc_in : c ∈ T := by rw [hTeq]; simp
    have ha_data := hT_mem_data a ha_in
    have hb_data := hT_mem_data b hb_in
    have hc_data := hT_mem_data c hc_in
    have ha_mem : a ∈ A := ha_data.1
    have hb_mem : b ∈ A := hb_data.1
    have hc_mem : c ∈ A := hc_data.1
    have ha_dist : dist a M.center = M.radius := ha_data.2
    have hb_dist : dist b M.center = M.radius := hb_data.2
    have hc_dist : dist c M.center = M.radius := hc_data.2
    have haO_norm : ‖a - M.center‖ = M.radius := by rw [← dist_eq_norm]; exact ha_dist
    have hbO_norm : ‖b - M.center‖ = M.radius := by rw [← dist_eq_norm]; exact hb_dist
    have hcO_norm : ‖c - M.center‖ = M.radius := by rw [← dist_eq_norm]; exact hc_dist
    -- Get barycentric coords from O ∈ conv {a, b, c}.
    have hO_conv : M.center ∈
        convexHull ℝ ((({a, b, c} : Finset ℝ²) : Set ℝ²)) := by
      have : M.center ∈ convexHull ℝ ((T : Finset ℝ²) : Set ℝ²) := hO_in_T
      rw [hTeq] at this; exact this
    obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hbary⟩ :=
      Problem97.MEC.mem_convexHull_three hab hbc hac hO_conv
    -- Three nonnegativity inequalities by cycling the barycentric lemma.
    have hac_norm : ‖a - M.center‖ = ‖c - M.center‖ := by rw [haO_norm, hcO_norm]
    have hbc_norm : ‖b - M.center‖ = ‖c - M.center‖ := by rw [hbO_norm, hcO_norm]
    have hba_norm : ‖b - M.center‖ = ‖a - M.center‖ := by rw [hbO_norm, haO_norm]
    have hca_norm : ‖c - M.center‖ = ‖a - M.center‖ := by rw [hcO_norm, haO_norm]
    have hab_norm : ‖a - M.center‖ = ‖b - M.center‖ := by rw [haO_norm, hbO_norm]
    have hcb_norm : ‖c - M.center‖ = ‖b - M.center‖ := by rw [hcO_norm, hbO_norm]
    -- For ⟨a - c, b - c⟩ ≥ 0: lemma directly (chord ab, apex c).
    have h_ac_bc : 0 ≤ ⟪a - c, b - c⟫_ℝ :=
      Problem97.MEC.inner_chord_nonneg_of_baryComb hac_norm hbc_norm hab hα hβ hγ hsum hbary.symm
    -- For ⟨b - a, c - a⟩ ≥ 0: apply lemma with relabel (a,b,c) → (b,c,a),
    -- weights (α,β,γ) → (β,γ,α).
    have hbary' : M.center = β • b + γ • c + α • a := by
      rw [← hbary]; module
    have h_ba_ca : 0 ≤ ⟪b - a, c - a⟫_ℝ :=
      Problem97.MEC.inner_chord_nonneg_of_baryComb hba_norm hca_norm hbc hβ hγ hα
        (by linarith) hbary'
    -- For ⟨c - b, a - b⟩ ≥ 0: relabel (a,b,c) → (c,a,b), weights (α,β,γ) → (γ,α,β).
    have hbary'' : M.center = γ • c + α • a + β • b := by
      rw [← hbary]; module
    have h_cb_ab : 0 ≤ ⟪c - b, a - b⟫_ℝ :=
      Problem97.MEC.inner_chord_nonneg_of_baryComb hcb_norm hab_norm (fun h => hac h.symm)
        hγ hα hβ (by linarith) hbary''
    exact ⟨a, b, c, ha_mem, hb_mem, hc_mem, hab, hbc, hac,
        ha_dist, hb_dist, hc_dist, h_ba_ca, h_cb_ab, h_ac_bc⟩

/- ### Wrapper into the existing `MoserTriangle` structure

The wrapper repackages a non-obtuse triple as a `MoserTriangle`.  We bundle
the inner-product inequalities together with the boundary triple so that
downstream consumers can extract both data and properties from a single
named record. -/

end Erdos9796CountingFragment_Erdos9796Proof_P97_Moser_TriangleNonObtuse
