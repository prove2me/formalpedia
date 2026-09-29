-- Prove2me | solution 1 for Problem97.MEC.mec_center_mem_convexHull_boundary
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:27.476593+00:00
-- url     : https://prove2.me/submissions/45169314-60e6-4c4b-8409-f1be266d885f

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.Moser.TriangleNonObtuse:4188:11841. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Definitions.Def_Erdos9796Counting_MEC_Boundary
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

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

/-- For nonempty `A`, the MEC radius is the max distance from the centre. -/
 lemma Problem97.MEC.mec_radius_eq_sup'
    (A : Finset ℝ²) (hA : A.Nonempty) :
    (mec A hA).radius =
      A.sup' hA (fun p => dist p (mec A hA).center) := by
  classical
  set M := mec A hA with hM_def
  -- M.radius ≤ sup' (use minimality with c = M.center, r = sup').
  have hsup_encl : ∀ p ∈ A,
      dist p M.center ≤ A.sup' hA (fun p => dist p M.center) := by
    intro p hp; exact Finset.le_sup' (fun p => dist p M.center) hp
  have hsup_min : M.radius ≤ A.sup' hA (fun p => dist p M.center) :=
    M.minimal M.center _ hsup_encl
  -- sup' ≤ M.radius (each distance is ≤ M.radius).
  have hsup_le : A.sup' hA (fun p => dist p M.center) ≤ M.radius :=
    (Finset.sup'_le_iff hA _).mpr (fun p hp => M.enclosing p hp)
  linarith

/-- For a nonempty finite set, some point attains the MEC radius and hence
lies on the boundary. -/
lemma Problem97.MEC.boundary_nonempty
    (A : Finset ℝ²) (hA : A.Nonempty) :
    (boundary A hA).Nonempty := by
  classical
  set M := mec A hA with hM_def
  -- Sup of `dist · M.center` over `A` is attained at some `p`.
  obtain ⟨p, hp_mem, hp_eq⟩ :=
    Finset.exists_mem_eq_sup' hA (fun p => dist p M.center)
  refine ⟨p, ?_⟩
  rw [mem_boundary_iff]
  refine ⟨hp_mem, ?_⟩
  -- dist p M.center = sup' = M.radius
  rw [← hp_eq, ← Problem97.MEC.mec_radius_eq_sup' A hA]





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

/-- Translating the centre by `t • v` changes the squared distance to `p` by
the standard quadratic in `t`:
`‖p - (c + t • v)‖² = ‖p - c‖² - 2 t · ⟪p - c, v⟫ + t² · ‖v‖²`. -/
 lemma Problem97.MEC.sq_dist_shrink_direction
    (p c v : ℝ²) (t : ℝ) :
    ‖p - (c + t • v)‖ ^ 2 =
      ‖p - c‖ ^ 2 - 2 * t * ⟪p - c, v⟫_ℝ + t ^ 2 * ‖v‖ ^ 2 := by
  have h1 : p - (c + t • v) = (p - c) - t • v := by abel_nf
  rw [h1, norm_sub_pow_two_real, real_inner_smul_right]
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Reduction from `x² < r²` and `0 ≤ x, 0 ≤ r` to `x < r`. -/
 lemma Problem97.MEC.lt_of_sq_lt_sq {x r : ℝ} (_hx : 0 ≤ x) (_hr : 0 ≤ r)
    (h : x ^ 2 < r ^ 2) : x < r := by
  nlinarith [sq_nonneg (x - r), sq_nonneg (x + r)]

/- ### MEC boundary set -/

-- Reuse MEC boundary lemmas from `MEC.Boundary` for a single canonical source
-- of `boundary`, `boundary_nonempty`, `mem_boundary_iff`, and `mec_radius_pos`.

/- ### Sub-lemma X: Welzl invariant -/


theorem solution
    {A : Finset ℝ²} (hA : A.Nonempty)
    (hncol : ¬ Collinear ℝ (A : Set ℝ²)) :
    (mec A hA).center ∈
      convexHull ℝ ((boundary A hA : Finset ℝ²) : Set ℝ²) := by
  classical
  set M := mec A hA with hM_def
  set B := boundary A hA with hB_def
  have hr_pos : 0 < M.radius := mec_radius_pos hA hncol
  have hB_ne : B.Nonempty := boundary_nonempty A hA
  -- conv(B) is convex, closed, nonempty, complete.
  have hcvx_convex : Convex ℝ (convexHull ℝ ((B : Finset ℝ²) : Set ℝ²)) :=
    convex_convexHull _ _
  have hB_fin : (B : Set ℝ²).Finite := B.finite_toSet
  have hcvx_closed : IsClosed (convexHull ℝ ((B : Finset ℝ²) : Set ℝ²)) :=
    hB_fin.isClosed_convexHull (𝕜 := ℝ)
  have hcvx_complete : IsComplete (convexHull ℝ ((B : Finset ℝ²) : Set ℝ²)) :=
    hcvx_closed.isComplete
  have hcvx_nonempty : (convexHull ℝ ((B : Finset ℝ²) : Set ℝ²)).Nonempty := by
    obtain ⟨p, hp⟩ := hB_ne
    exact ⟨p, subset_convexHull _ _ (by exact_mod_cast hp)⟩
  by_contra hO_not
  obtain ⟨v, hv_mem, hv_min⟩ :=
    exists_norm_eq_iInf_of_complete_convex hcvx_nonempty hcvx_complete hcvx_convex M.center
  have hv_ne : v ≠ M.center := fun h => hO_not (h ▸ hv_mem)
  set d := v - M.center with hd_def
  have hd_pos : 0 < ‖d‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv_ne)
  have hd_sq_pos : 0 < ‖d‖ ^ 2 := by positivity
  -- Separating-direction inequality: `‖d‖² ≤ ⟪p - O, d⟫` for `p ∈ conv B`.
  have hsep : ∀ p ∈ convexHull ℝ ((B : Finset ℝ²) : Set ℝ²),
      ‖d‖ ^ 2 ≤ ⟪p - M.center, d⟫_ℝ := by
    intro p hp
    have hker := (norm_eq_iInf_iff_real_inner_le_zero hcvx_convex hv_mem).mp hv_min p hp
    have h1 : ⟪p - M.center, d⟫_ℝ = ⟪p - v, d⟫_ℝ + ‖d‖ ^ 2 := by
      have heq : p - M.center = (p - v) + d := by rw [hd_def]; abel
      rw [heq, inner_add_left, real_inner_self_eq_norm_sq]
    have h2 : ⟪p - v, d⟫_ℝ = -⟪M.center - v, p - v⟫_ℝ := by
      rw [hd_def, show v - M.center = -(M.center - v) from by abel,
          inner_neg_right, real_inner_comm]
    linarith
  have hsep_B : ∀ p ∈ B, ‖d‖ ^ 2 ≤ ⟪p - M.center, d⟫_ℝ :=
    fun p hp => hsep p (subset_convexHull _ _ (by exact_mod_cast hp))
  -- Interior set I = A \ B (every q ∈ I has dist q O < r).
  set I := A.filter (fun q => q ∉ B) with hI_def
  have hI_strict : ∀ q ∈ I, dist q M.center < M.radius := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqA, hq_not⟩
    have hq_le : dist q M.center ≤ M.radius := M.enclosing q hqA
    rcases lt_or_eq_of_le hq_le with hlt | heq
    · exact hlt
    · exfalso; apply hq_not
      exact (mem_boundary_iff hA).2 ⟨hqA, heq⟩
  -- Strict gap from interior (use `max + ε` style).
  -- δ := M.radius - Imax > 0 when I nonempty; we then choose `t` accordingly.
  -- When I = ∅, choose t = 1 (or anything in (0, 2)).
  -- Common bookkeeping: pick t ∈ (0, 1] with `t * ‖d‖ < δ` (δ := r if I = ∅).
  set δ : ℝ := if hne : I.Nonempty then
      M.radius - I.sup' hne (fun q => dist q M.center) else M.radius
    with hδ_def
  have hδ_pos : 0 < δ := by
    by_cases hI_ne : I.Nonempty
    · rw [hδ_def, dif_pos hI_ne]
      have : I.sup' hI_ne (fun q => dist q M.center) < M.radius :=
        (Finset.sup'_lt_iff hI_ne).mpr hI_strict
      linarith
    · rw [hδ_def, dif_neg hI_ne]; exact hr_pos
  -- Choose `t = min 1 (δ / (2 * ‖d‖))`.
  set t := min 1 (δ / (2 * ‖d‖)) with ht_def
  have ht_pos : 0 < t := lt_min (by norm_num) (by positivity)
  have ht_le_one : t ≤ 1 := min_le_left _ _
  have ht_le_δd : t ≤ δ / (2 * ‖d‖) := min_le_right _ _
  have ht_d_lt_δ : t * ‖d‖ < δ := by
    have h1 : t * ‖d‖ ≤ (δ / (2 * ‖d‖)) * ‖d‖ :=
      mul_le_mul_of_nonneg_right ht_le_δd (le_of_lt hd_pos)
    have h2 : (δ / (2 * ‖d‖)) * ‖d‖ = δ / 2 := by field_simp
    rw [h2] at h1; linarith
  set c' := M.center + t • d with hc'_def
  -- Bound for p ∈ B:  `dist p c' < M.radius`.
  have hp_dist_lt : ∀ p ∈ B, dist p c' < M.radius := by
    intro p hp
    have hsep_p := hsep_B p hp
    have hp_data := (mem_boundary_iff hA).1 hp
    have hp_bdry : dist p M.center = M.radius := hp_data.2
    have hp_norm : ‖p - M.center‖ = M.radius := by
      rw [← dist_eq_norm]; exact hp_bdry
    -- ‖p - c'‖² = M.radius² - 2 t ⟪p - O, d⟫ + t² ‖d‖²
    --          ≤ M.radius² - 2 t ‖d‖² + t² ‖d‖²
    --          = M.radius² + (t² - 2t) ‖d‖²  <  M.radius²  for t ∈ (0,1].
    have hsq_eq : ‖p - c'‖ ^ 2
        = ‖p - M.center‖ ^ 2 - 2 * t * ⟪p - M.center, d⟫_ℝ + t ^ 2 * ‖d‖ ^ 2 := by
      rw [hc'_def]; exact Problem97.MEC.sq_dist_shrink_direction p M.center d t
    have ht_lin_bound : -2 * t * ⟪p - M.center, d⟫_ℝ ≤ -2 * t * ‖d‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hsep_p (le_of_lt ht_pos)
      linarith
    have hsq_le : ‖p - c'‖ ^ 2 ≤ M.radius ^ 2 + (t ^ 2 - 2 * t) * ‖d‖ ^ 2 := by
      rw [hp_norm] at hsq_eq
      linarith [hsq_eq, ht_lin_bound]
    have hpoly_neg : (t ^ 2 - 2 * t) * ‖d‖ ^ 2 < 0 := by
      have hpoly : t ^ 2 - 2 * t < 0 := by nlinarith
      exact mul_neg_of_neg_of_pos hpoly hd_sq_pos
    have hsq_lt : ‖p - c'‖ ^ 2 < M.radius ^ 2 := by linarith
    rw [dist_eq_norm]
    exact Problem97.MEC.lt_of_sq_lt_sq (norm_nonneg _) M.radius_nn hsq_lt
  -- Bound for q ∈ I:  `dist q c' < M.radius`.
  have hq_dist_lt : ∀ q ∈ I, dist q c' < M.radius := by
    intro q hq
    have hq_bound : dist q c' ≤ dist q M.center + t * ‖d‖ := by
      rw [hc'_def, dist_eq_norm]
      have heq : q - (M.center + t • d) = (q - M.center) - t • d := by abel_nf
      rw [heq]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos,
          show ‖q - M.center‖ = dist q M.center from (dist_eq_norm _ _).symm]
    -- Interior gap: dist q M.center ≤ I.sup' = M.radius - δ.
    have hq_Imax_lt : dist q M.center + t * ‖d‖ < M.radius := by
      have hI_ne : I.Nonempty := ⟨q, hq⟩
      have hsup_eq : I.sup' hI_ne (fun q => dist q M.center) = M.radius - δ := by
        simp only [hδ_def, hI_ne, dif_pos]; ring
      have hq_sup : dist q M.center ≤ I.sup' hI_ne (fun q => dist q M.center) :=
        Finset.le_sup' (f := fun q => dist q M.center) hq
      rw [hsup_eq] at hq_sup
      linarith
    linarith
  -- Conclude: every distance from c' is < M.radius; contradicts minimality.
  have h_all_lt : ∀ q ∈ A, dist q c' < M.radius := by
    intro q hq
    by_cases hqB : q ∈ B
    · exact hp_dist_lt q hqB
    · exact hq_dist_lt q (Finset.mem_filter.mpr ⟨hq, hqB⟩)
  set r' := A.sup' hA (fun q => dist q c') with hr'_def
  have hr'_lt : r' < M.radius := (Finset.sup'_lt_iff hA).mpr h_all_lt
  have hr'_encl : ∀ q ∈ A, dist q c' ≤ r' :=
    fun q hq => Finset.le_sup' (f := fun q => dist q c') hq
  have hmin : M.radius ≤ r' := M.minimal c' r' hr'_encl
  linarith

/- ### Diameter (Thales) auxiliaries -/







/- ### Barycentric (card 3) case -/











/- ### Carathéodory cardinality bound in dim 2 -/



/- ### Conversion of `convexHull` of small Finsets to explicit barycentric form -/







/- ### Main extraction theorem -/



/- ### Wrapper into the existing `MoserTriangle` structure

The wrapper repackages a non-obtuse triple as a `MoserTriangle`.  We bundle
the inner-product inequalities together with the boundary triple so that
downstream consumers can extract both data and properties from a single
named record. -/

end Erdos9796CountingFragment_Erdos9796Proof_P97_Moser_TriangleNonObtuse
