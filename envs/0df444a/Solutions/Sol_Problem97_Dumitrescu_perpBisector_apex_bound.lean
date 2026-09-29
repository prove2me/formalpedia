-- Prove2me | solution 1 for Problem97.Dumitrescu.perpBisector_apex_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:16.861991+00:00
-- url     : https://prove2.me/submissions/33f7ce44-d43b-4f48-8809-624f7435e12a

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.Dumitrescu.L1:5879:8560. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Hull
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

section Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_L1

open Problem97 Problem97.Dumitrescu

/- Fragment from Erdos9796Proof.P97.Dumitrescu.L1; source SHA-256 170e1886e820b6afa033edfc08e0c4f73057cb7f3c71cc97552cede97ff21fbf -/


/-!
# Dumitrescu L1: perpendicular-bisector apex bound (Problem 97)

`Problem97.Dumitrescu.perpBisector_apex_bound` is Dumitrescu's Lemma 1
(Dumitrescu 2006 / Nivasch–Pach–Pinchasi–Zerbib 2013, arXiv:1207.1266 §2):

  For any convex-independent finite point set `A ⊆ ℝ²` and any base edge
  `(a, b)` with `a, b ∈ A` and `a ≠ b`, at most `2` points of `A` lie on
  the perpendicular bisector of the segment `ab`.

This is the "perpendicular-bisector apex bound" used in the
isosceles-count double-count argument. It corresponds to the blueprint
obligation `p97-dumitrescu-l1-perp-bisector-apex`.

## Proof strategy

A point `p` lies on the perpendicular bisector of `ab` iff
`dist p a = dist p b` (Mathlib's `AffineSubspace.mem_perpBisector_iff_dist_eq`).

Suppose, for contradiction, that three distinct points `p, q, r ∈ A` all
lie on this perpendicular bisector. Then:

* `q -ᵥ p` and `r -ᵥ p` both lie in the direction of the perpendicular
  bisector, which equals `(ℝ ∙ (b -ᵥ a))ᗮ`
  (Mathlib's `AffineSubspace.direction_perpBisector`).
* In `EuclideanSpace ℝ (Fin 2)`, this orthogonal complement has dimension
  `1` (since `a ≠ b` makes `b -ᵥ a` nonzero, and
  `Submodule.finrank_orthogonal_span_singleton` then gives finrank `1`).
* `q -ᵥ p ≠ 0` (since `p ≠ q`), so `ℝ ∙ (q -ᵥ p)` and `(ℝ ∙ (b -ᵥ a))ᗮ`
  are two `1`-dimensional subspaces of `ℝ²` with the first contained in
  the second, hence equal (`Submodule.eq_of_le_of_finrank_eq`).
* In particular `r -ᵥ p ∈ ℝ ∙ (q -ᵥ p)`, so `r -ᵥ p` is a scalar
  multiple of `q -ᵥ p`. This gives `Collinear ℝ {p, q, r}` directly via
  `collinear_iff_of_mem` (each point is a scalar multiple of `q -ᵥ p`
  added to `p`).

Once `{p, q, r}` is collinear, `Collinear.wbtw_or_wbtw_or_wbtw` says one
of the three lies on the segment between the other two. That point then
lies in the convex hull of the other two, which is a subset of
`convexHull ℝ (A \ {it})`, contradicting `ConvexIndep A`.

## References

* Adrian Dumitrescu (2006), *On Distinct Distances from a Vertex of a Convex Polygon*, Discrete & Computational Geometry 36, 503–509. DOI: 10.1007/s00454-006-1262-y.
* Gabriel Nivasch, János Pach, Rom Pinchasi, and Shira Zerbib, *The Number of Distinct Distances from a Vertex of a Convex Polygon*, Journal of Computational Geometry 4 (2013), 1–12; arXiv:1207.1266 (2012 preprint).
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical




/-- Three points on the perpendicular bisector of `ab` in `ℝ²` are
collinear, when `a ≠ b` and two of the three points are distinct.

The key fact is that the direction of the perpendicular bisector is
`(ℝ ∙ (b -ᵥ a))ᗮ`, which in `EuclideanSpace ℝ (Fin 2)` is
`1`-dimensional. Two `1`-dimensional subspaces of `ℝ²`, one containing
the other, coincide. -/
 lemma Problem97.Dumitrescu.collinear_of_three_on_perpBisector
    {a b p q r : ℝ²} (hab : a ≠ b)
    (hpeq : dist p a = dist p b) (hqeq : dist q a = dist q b)
    (hreq : dist r a = dist r b) (hpq : p ≠ q) :
    Collinear ℝ ({p, q, r} : Set ℝ²) := by
  -- `b -ᵥ a ≠ 0` (used to obtain a 1-dim orthogonal complement in ℝ²).
  have hbma_ne : b -ᵥ a ≠ 0 := vsub_ne_zero.mpr (Ne.symm hab)
  -- The three points all lie in the perpendicular bisector.
  have hp_mem : p ∈ AffineSubspace.perpBisector a b :=
    (AffineSubspace.mem_perpBisector_iff_dist_eq).mpr hpeq
  have hq_mem : q ∈ AffineSubspace.perpBisector a b :=
    (AffineSubspace.mem_perpBisector_iff_dist_eq).mpr hqeq
  have hr_mem : r ∈ AffineSubspace.perpBisector a b :=
    (AffineSubspace.mem_perpBisector_iff_dist_eq).mpr hreq
  -- `q -ᵥ p` and `r -ᵥ p` lie in the direction `(ℝ ∙ (b -ᵥ a))ᗮ`.
  have hqp_in_dir : q -ᵥ p ∈ (ℝ ∙ (b -ᵥ a))ᗮ := by
    rw [← AffineSubspace.direction_perpBisector]
    exact AffineSubspace.vsub_mem_direction hq_mem hp_mem
  have hrp_in_dir : r -ᵥ p ∈ (ℝ ∙ (b -ᵥ a))ᗮ := by
    rw [← AffineSubspace.direction_perpBisector]
    exact AffineSubspace.vsub_mem_direction hr_mem hp_mem
  -- `q -ᵥ p ≠ 0` since `p ≠ q`.
  have hqp_ne : q -ᵥ p ≠ 0 := vsub_ne_zero.mpr (Ne.symm hpq)
  -- finrank `(ℝ ∙ (b -ᵥ a))ᗮ = 1`, using `finrank ℝ ℝ² = 1 + 1`.
  have hfin : Fact (Module.finrank ℝ ℝ² = 1 + 1) :=
    ⟨fact_finrank_euclideanSpace_fin_two.out⟩
  have hfr_orth : Module.finrank ℝ (↥((ℝ ∙ (b -ᵥ a))ᗮ)) = 1 :=
    Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (E := ℝ²) (n := 1) hbma_ne
  -- finrank `ℝ ∙ (q -ᵥ p) = 1` since `q -ᵥ p ≠ 0`.
  have hfr_span : Module.finrank ℝ (↥(ℝ ∙ (q -ᵥ p))) = 1 := finrank_span_singleton hqp_ne
  -- `ℝ ∙ (q -ᵥ p) ≤ (ℝ ∙ (b -ᵥ a))ᗮ` since `q -ᵥ p` lies there.
  have hsub : (ℝ ∙ (q -ᵥ p)) ≤ (ℝ ∙ (b -ᵥ a))ᗮ := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact hqp_in_dir
  -- They are equal: both `1`-dim, one inside the other.
  have heq : (ℝ ∙ (q -ᵥ p)) = (ℝ ∙ (b -ᵥ a))ᗮ :=
    Submodule.eq_of_le_of_finrank_eq hsub (hfr_span.trans hfr_orth.symm)
  -- So `r -ᵥ p ∈ ℝ ∙ (q -ᵥ p)`, i.e. `r -ᵥ p = t • (q -ᵥ p)` for some `t`.
  have hrp_in_span : r -ᵥ p ∈ ℝ ∙ (q -ᵥ p) := by rw [heq]; exact hrp_in_dir
  rcases Submodule.mem_span_singleton.mp hrp_in_span with ⟨t, ht⟩
  -- Assemble the collinearity witness with base `p` and direction `q -ᵥ p`.
  rw [collinear_iff_of_mem (show p ∈ ({p, q, r} : Set ℝ²) from Or.inl rfl)]
  refine ⟨q -ᵥ p, ?_⟩
  intro x hx
  rcases hx with rfl | hx
  · exact ⟨0, by simp⟩
  rcases hx with rfl | hx
  · exact ⟨1, by simp⟩
  rcases hx with rfl
  exact ⟨t, by rw [eq_vadd_iff_vsub_eq, ← ht]⟩


theorem solution
    {A : Finset ℝ²} (hA : ConvexIndep A)
    {a b : ℝ²} (_ha : a ∈ A) (_hb : b ∈ A) (hab : a ≠ b) :
    (A.filter (fun p => dist p a = dist p b)).card ≤ 2 := by
  -- Assume, for contradiction, three distinct equidistant points.
  by_contra h
  push_neg at h
  rw [Finset.two_lt_card] at h
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := h
  rcases Finset.mem_filter.mp hp with ⟨hpA, hpeq⟩
  rcases Finset.mem_filter.mp hq with ⟨hqA, hqeq⟩
  rcases Finset.mem_filter.mp hr with ⟨hrA, hreq⟩
  -- Three perpBisector points in 2D are collinear.
  have hcol : Collinear ℝ ({p, q, r} : Set ℝ²) :=
    Problem97.Dumitrescu.collinear_of_three_on_perpBisector hab hpeq hqeq hreq hpq
  -- By the wbtw-trichotomy, one of `p, q, r` lies between the other two.
  rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
  · -- Case `Wbtw p q r`: `q ∈ segment p r ⊆ convexHull (A \ {q})`.
    apply hA q hqA
    have hseg : q ∈ segment ℝ p r := hw.mem_segment
    rw [← convexHull_pair] at hseg
    have hsub : ({p, r} : Set ℝ²) ⊆ ((A : Set ℝ²) \ {q}) := by
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨hpA, by simp only [Set.mem_singleton_iff]; exact hpq⟩
      rcases hx with rfl
      exact ⟨hrA, by simp only [Set.mem_singleton_iff]; exact Ne.symm hqr⟩
    exact convexHull_mono hsub hseg
  · -- Case `Wbtw q r p`: `r ∈ segment q p ⊆ convexHull (A \ {r})`.
    apply hA r hrA
    have hseg : r ∈ segment ℝ q p := hw.mem_segment
    rw [← convexHull_pair] at hseg
    have hsub : ({q, p} : Set ℝ²) ⊆ ((A : Set ℝ²) \ {r}) := by
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨hqA, by simp only [Set.mem_singleton_iff]; exact hqr⟩
      rcases hx with rfl
      exact ⟨hpA, by simp only [Set.mem_singleton_iff]; exact hpr⟩
    exact convexHull_mono hsub hseg
  · -- Case `Wbtw r p q`: `p ∈ segment r q ⊆ convexHull (A \ {p})`.
    apply hA p hpA
    have hseg : p ∈ segment ℝ r q := hw.mem_segment
    rw [← convexHull_pair] at hseg
    have hsub : ({r, q} : Set ℝ²) ⊆ ((A : Set ℝ²) \ {p}) := by
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨hrA, by simp only [Set.mem_singleton_iff]; exact Ne.symm hpr⟩
      rcases hx with rfl
      exact ⟨hqA, by simp only [Set.mem_singleton_iff]; exact Ne.symm hpq⟩
    exact convexHull_mono hsub hseg

end Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_L1
