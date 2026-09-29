-- Prove2me | solution 1 for Problem97.inner_chord_eq_dist_sq_diff
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:18.396378+00:00
-- url     : https://prove2.me/submissions/57c6f78b-090d-456f-aa86-dce41442cb20

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.Dumitrescu.Lc1Strict:7235:8786. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Geometry.Euclidean.Triangle

section Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_Lc1Strict

open Problem97

/- Fragment from Erdos9796Proof.P97.Dumitrescu.Lc1Strict; source SHA-256 79552d47d9473f42104d5850f982510576893e85ddd7347652348a1f8b91502b -/



/-!
# Perpendicular-bisector half-plane comparison

This file deposits the **load-bearing chord-side / half-plane lemma**
used by Nivasch–Pach–Pinchasi–Zerbib 2013 Lemma 6 (the witness-monotonicity argument that
underlies both Dumitrescu L5 `CapWitnessRanking` and Dumitrescu Lc3
`CapDiagonalVertexProfile`).

## Paper provenance

Nivasch–Pach–Pinchasi–Zerbib 2013 (arXiv:1207.1266) §2 Lemma 6 begins its proof with:

> "We have `|yc| ≥ |ya| = |yb|`."

The "`|yc| ≥ |ya|`" half of this chain is **not** a consequence of
strict-monotone-distance along a cap arc (which would require all cap
points to lie on the MEC sphere — they don't, in our setup). It is a
**linear-algebra** fact about which side of the perpendicular bisector
of `ac` the point `y` sits on:

* `x` witnesses edge `ac` ⟹ `x` lies on the perpendicular bisector of
  `ac` (`dist x a = dist x c`).
* `y` "between `a` and `x` in convex order" ⟹ `y` lies on the closed
  half-plane on `a`'s side of the perpendicular bisector of `ac` (this
  is the convex-position consequence — *open* and not in scope here).
* Once `y` is on `a`'s side of the perpendicular bisector, the
  comparison `|ya| ≤ |yc|` is immediate from the polarisation identity.

This file proves the **third bullet** in isolation as a clean Mathlib-
style inner-product lemma. The second bullet (convex order ⟹ half-plane
side) is the **genuinely missing piece** of the Lemma 6 proof in our
setting and is **not** discharged here — see the "What's NOT in this
file" section below for the precise statement of the open obligation.

## What IS in this file (provable today)

### `inner_chord_eq_dist_sq_diff` (polarisation identity)

For any three points `a, c, y : ℝ²`:
```
2 * ⟪y - midpoint a c, c - a⟫_ℝ = dist y a ^ 2 - dist y c ^ 2.
```

This is the central algebraic identity. Pure inner-product algebra;
no geometry. The signed quantity on the left is the **chord-side
test** ("which side of the perpendicular bisector of `ac` does `y` lie
on?") and the right-hand side is the **distance-comparison test**.

### `dist_le_iff_inner_chord_nonpos`

Direct equivalence: `dist y a ≤ dist y c ↔ ⟪y - m, c - a⟫_ℝ ≤ 0`,
where `m = midpoint a c`. This is what Lemma 6's chain
"`|yc| ≥ |ya|`" needs as its *input*.

### `dist_lt_iff_inner_chord_neg`

Strict variant: `dist y a < dist y c ↔ ⟪y - m, c - a⟫_ℝ < 0`.

### `dist_le_of_inner_chord_le_zero`

The "easy direction" packaged as a stand-alone implication: the
algebraic chord-side condition implies the distance comparison.

### `same_side_perpBisector_dist_le`

Cap-witness flavored re-statement: if `x` witnesses edge `(a, c)`
(`dist x a = dist x c`) and `y` lies on `a`'s closed half-plane of the
perpendicular bisector of `ac` (`⟪y - x, c - a⟫_ℝ ≤ 0`), then
`dist y a ≤ dist y c`.

## What is NOT in this file (Lemma 6's gap)

Nivasch–Pach–Pinchasi–Zerbib Lemma 6's actual proof requires three more ingredients that
are **all open** in the current infrastructure:

### Gap 1 — `convex_order_implies_perpBisector_side`  (NOT proven)

For four points `a, y, x, c` in `ℝ²` in **convex position**, with
convex polygon order `a, y, x, ..., c, ...` (i.e. `y` strictly between
`a` and `x` in the polygon ordering, and `x` strictly between `a` and
`c`), and `x` on the perpendicular bisector of `ac`, then `y` lies on
`a`'s side of that perpendicular bisector:

```text
⟪y - midpoint a c, c - a⟫_ℝ ≤ 0.
```

This is the "second bullet" of the Lemma 6 chain. **It requires a
convex-position angular monotonicity argument** that is not in current
infrastructure: as `y` moves along the convex polygon from `a` towards
`x`, the chord-side projection on the perp bisector of `ac` is
monotone. The argument uses general-position convexity, not just the
chord-side / disk-containment data we currently package.

### Gap 2 — wedge containment (`∠acb ≤ ∠ycb`)  (NOT proven)

Nivasch–Pach–Pinchasi–Zerbib Lemma 6 then derives a contradiction by combining
`∠acb ≥ π/2` (cap-Thales at the cap-endpoint chord) with
`∠ycb ≤ π/2` (chord-side argument inside △ycb using `|yc| ≥ |yb|`)
**and** the wedge containment `∠acb ≤ ∠ycb`. The last piece — that the
angle subtended at `c` by `ab` is at most the angle subtended by `yb`
— is another convex-position monotonicity statement, similarly not in
current infrastructure.

### Gap 3 — cap-Thales-at-all-triples generalization  (NOT proven)

Definition 3 of Nivasch–Pach–Pinchasi–Zerbib 2013 (p. 4) gives a cap-Thales iff at the
*cap endpoints*. Our `inner_nonpos_of_cap_region_thales` discharges
this in `lc1_capArcThales_C{1,2,3}` for cap-points subtending the
*Moser-vertex chord* — exactly the cap-endpoint case. The diagonal-
vertex argument (Dumitrescu §2 p. 3-4 / Nivasch–Pach–Pinchasi–Zerbib Corollary 7 proof)
**does not require the all-triples generalization** — it composes
Lemma 6 (applied with various choices of cap endpoints) with the
positional constraint. So Gap 3 is *not* on the Lemma 6 critical
path, but is flagged here for completeness.

## Composition status

This file by itself **does not close** either L5 `CapWitnessRanking`
constructor or Lc3 strong-form `CapDiagonalVertexProfile`. Closing
Lemma 6 — and through it both downstream targets — requires Gap 1 +
Gap 2 above, which are **out of scope for this dispatch** by the
brief's "if genuinely unprovable from current infrastructure, surface
the gap" guidance.

The half-plane comparison lemma here is a clean, axiom-clean,
self-contained Mathlib-style deposit. When the convex-order /
perpendicular-bisector half-plane bridge is later landed (Gap 1),
together with the wedge containment (Gap 2), Lemma 6 will compose
without further analytic work.

## References

* Gabriel Nivasch, János Pach, Rom Pinchasi, and Shira Zerbib, *The Number of Distinct Distances from a Vertex of a Convex Polygon*, Journal of Computational Geometry 4 (2013), 1–12; arXiv:1207.1266 (2012 preprint).
* Adrian Dumitrescu (2006), *On Distinct Distances from a Vertex of a Convex Polygon*, Discrete & Computational Geometry 36, 503–509. DOI: 10.1007/s00454-006-1262-y. Lemma 2, Corollary 1 (p. 3-4).
-/

open scoped EuclideanGeometry InnerProductSpace
open Finset



/- ### Polarisation identity for the perpendicular-bisector half-plane test

The central algebraic fact: the signed "chord-side test"
`⟪y - midpoint a c, c - a⟫_ℝ` and the squared-distance comparison
`dist y a ^ 2 - dist y c ^ 2` are related by a factor of 2. From this
one identity all four "perpendicular bisector half-plane vs distance
comparison" lemmas in this file follow by basic real algebra.

The identity expands `dist y a ^ 2 - dist y c ^ 2` via
`norm_sub_sq_real`:
```
dist y a ^ 2 = ‖y - a‖^2 = ‖y‖^2 - 2 ⟪y, a⟫ + ‖a‖^2,
dist y c ^ 2 = ‖y - c‖^2 = ‖y‖^2 - 2 ⟪y, c⟫ + ‖c‖^2.
```
Subtracting and rearranging:
```
dist y a ^ 2 - dist y c ^ 2
  = 2 ⟪y, c - a⟫ + (‖a‖^2 - ‖c‖^2)
  = 2 ⟪y, c - a⟫ - ⟪a + c, c - a⟫
  = ⟪2 y - (a + c), c - a⟫
  = 2 ⟪y - midpoint a c, c - a⟫,
```
since `midpoint a c = (a + c) / 2`, hence `2 · midpoint a c = a + c`.

This gives the stated form. -/


theorem solution (a c y : ℝ²) :
    2 * ⟪y - midpoint ℝ a c, c - a⟫_ℝ
      = dist y a ^ 2 - dist y c ^ 2 := by
  -- Coordinate-wise polynomial identity in ℝ² = EuclideanSpace ℝ (Fin 2).
  have norm_sub_sq : ∀ (x y : ℝ²),
      ‖x - y‖ ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := fun x y => by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, sq_abs, Real.norm_eq_abs, PiLp.sub_apply]
  have inner_eq : ∀ (a b : ℝ²),
      ⟪a, b⟫_ℝ = a 0 * b 0 + a 1 * b 1 := fun a b => by
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_two, mul_comm (a _) (b _)]
  have hmid : ∀ i : Fin 2, (midpoint ℝ a c) i = ((a i + c i) : ℝ) / 2 := by
    intro i; rw [midpoint_eq_smul_add]
    simp [PiLp.smul_apply, PiLp.add_apply, invOf_eq_inv]; ring
  rw [dist_eq_norm, dist_eq_norm, norm_sub_sq, norm_sub_sq, inner_eq]
  simp only [PiLp.sub_apply, hmid]
  ring

/- ### Distance comparison ↔ chord-side half-plane condition

The polarisation identity gives a clean iff:
```
dist y a ≤ dist y c ↔ ⟪y - midpoint a c, c - a⟫_ℝ ≤ 0.
```
Both sides are equivalent to "`y` is on the closed half-plane on `a`'s
side of the perpendicular bisector of `ac`." -/









/- ### Cap-witness flavored re-statement

In the Nivasch–Pach–Pinchasi–Zerbib Lemma 6 setting, the role of `midpoint a c` is filled
by the **witness** `x` for edge `ac`: `x` lies on the perpendicular
bisector of `ac`, i.e. `dist x a = dist x c`. The half-plane side test
through `x` is then equivalent (modulo translation along the bisector)
to the half-plane side test through `midpoint a c`, because both lie
on the perpendicular bisector line.

The "same side" condition expressed via `x` directly:
`⟪y - x, c - a⟫_ℝ ≤ 0` (i.e. `y - x` has nonpositive projection on
`c - a`, so `y` lies on `a`'s side of the line through `x` perpendicular
to `ac`). Since `x` is on the perpendicular bisector, the perpendicular
line through `x` to `ac` IS the perpendicular bisector itself.

The bridge from "`y - x` chord-side" to "`y - midpoint a c` chord-side"
uses the fact that `x - midpoint a c` is perpendicular to `c - a`. -/







/- ### Mathlib bridge — relation to `AffineSubspace.perpBisector`

The inner-product form `⟪y - x, c - a⟫_ℝ ≤ 0` matches Mathlib's
`AffineSubspace.perpBisector` characterizations. We expose the bridge
so future Lemma 6 work can quote either form.

Specifically: `c ∈ AffineSubspace.perpBisector a b ↔ dist c a = dist c b`
(`AffineSubspace.mem_perpBisector_iff_dist_eq` in Mathlib). The
displacement `y - x` (with `x` on the perp bisector) projected on
`c - a` is `≤ 0` iff `y - x` points "away" from `c`, iff `y` is on
`a`'s side. -/





/- ### Companion: trivially-symmetric corollary at zero

When `y = x` (i.e. `y` IS the witness, on the perpendicular bisector
exactly), both sides of the half-plane condition collapse to `0`,
yielding `dist y a = dist y c` (witness symmetry). This is recorded
for completeness as a sanity check on the half-plane formulation. -/

end Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_Lc1Strict
