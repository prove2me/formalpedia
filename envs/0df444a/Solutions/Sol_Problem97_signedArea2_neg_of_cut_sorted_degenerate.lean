-- Prove2me | solution 1 for Problem97.signedArea2_neg_of_cut_sorted_degenerate
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:44.37242+00:00
-- url     : https://prove2.me/submissions/98f82d85-99f6-4f08-a2b5-896cc4e5fc6d

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.ConvexCyclicOrder.Construct:80226:83042. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_ConvexCyclicOrder_Construct
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_ArcAngle
import Definitions.Def_Erdos9796Counting_SignedAreaOangle
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.Finset.Sort
import Theorems.Thm_Problem97_center_mem_openSegment_of_arcAngle_gap_eq_neg_pi
import Theorems.Thm_Problem97_notMem_convexHull_diff_convexHull_of_notMem
import Theorems.Thm_Problem97_notMem_extremePoints_of_mem_interior
import Theorems.Thm_Problem97_signedArea2_sign_eq_oangle_sign

section Erdos9796CountingFragment_Erdos9796Proof_P97_MEC_ArcAngle

open Problem97

/- Fragment from Erdos9796Proof.P97.MEC.ArcAngle; source SHA-256 4d7ceebcbb8adcb5f2581ad54e00ef84ce109370fabe4fdf83c165b1fc179150 -/


/-!
# MEC arc-angle parametrization — A0 (definition + algebra)

This file introduces `Problem97.arcAngle center p : Real.Angle`, the oriented
angle in `ℝ / 2πℤ` between the canonical first basis vector
`EuclideanSpace.basisFun (Fin 2) ℝ 0` and the chord `p - center`. Geometrically
this is the angular position of `p` on a circle centered at `center`, measured
from the `+x` direction in the standard counter-clockwise orientation of `ℝ²`.

## Why `Real.Angle` rather than `ℝ`

The natural alternative — `Complex.arg : ℂ → ℝ` with range `(-π, π]` — forces a
branch cut through the negative `x`-axis. Caps in the MEC analysis routinely
straddle this cut and every monotonicity lemma would need to case-split on it.
Quotienting by `2π` (i.e. landing in `Real.Angle = ℝ / 2πℤ`) eliminates the
branch cut. Signed circular differences (`arcAngle p − arcAngle q`) are then
well-defined and compose cleanly via `Orientation.oangle` algebra.

## Cross-reference

See `docs/97-arc-angle-parametrization-plan.md` § "A0 — `arcAngle` definition +
algebra" for the four-step program (A0 + A1 + A2 + A3).

## Status — A0 + A1 + A2 + A3 (plus A3-iff)

This file establishes the full A0-A3 program plus the equality / iff forms of
A3 added by the Dumitrescu Lc1 dispatch (2026-05-22):

* `arcAngle` definition.
* Identity 1: `arcAngle_center_self` — at the apex itself the angle is `0`.
* Identity 2: `arcAngle_sub_arcAngle` — the central subtraction bridge to
  `Orientation.oangle` on the chord vectors. **Load-bearing** for downstream
  A1/A2/A3.
* Identity 3: `arcAngle_neg` — antipodal reflection adds `π`.
* A1 — `onArcOpposite_iff_oangle_sign_mul`: chord-side `OnArcOpposite vi vj vk v`
  is equivalent to the product of two `Orientation.oangle` signs being `≤ 0`.
  This is the inscribed-angle form (oangles centered at the test points `v` and
  `vi`, not at the MEC center).
* A1 — `onArcOpposite_iff_arcAngle_sign_mul`: the same iff restated as a sign
  product of arc-angle differences, by applying `arcAngle_sub_arcAngle` with the
  test point itself as the center. This is the form downstream consumers (Lc1,
  Nivasch–Pach–Pinchasi–Zerbib L6, the U-sequence geometric core) read out of A1.
* A2 — `arcAngle_chord_length` chord-length formula `dist p q = 2 r |sin(Δ/2)|`.
* A3 — `arcAngle_chord_length_strict_mono` strict monotonicity of chord length
  in arc-angle difference; analytic core `abs_sin_half_strict_mono`.
* **A3-iff** (Dumitrescu Lc1 dispatch, 2026-05-22): the equality and `<` iff
  forms `arcAngle_chord_length_eq_iff`, `arcAngle_chord_length_lt_iff`, and
  their analytic counterparts `abs_sin_half_eq_iff`, `abs_sin_half_lt_iff`.
  The equality form is the load-bearing input to the Dumitrescu witness-pair
  ranking argument: "two MEC-arc points equidistant from a third MEC-arc
  point have arc-angle differences equal in absolute value" — exactly the
  arc-symmetry-about-the-apex assertion the Lc1 diagonal-vertex argument
  needs to convert "common apex" into a positional constraint.

## Sign / argument-order convention for Identity 2

The conclusion of `arcAngle_sub_arcAngle` is

```
arcAngle center p - arcAngle center q
  = stdOrientation.oangle (q - center) (p - center)
```

i.e. with `q - center` **first** and `p - center` **second** on the right. This
matches the direct consequence of `Orientation.oangle_sub_left` and is the
mathematically correct direction. The scoping report tentatively wrote the RHS
arguments in the opposite order; that order would flip the sign relative to
this lemma. Downstream consumers (A1's `OnArcOpposite` bridge,
`signedArea2_sign_eq_oangle_sign`) read the chord endpoints out of the
right-hand `oangle`, so when composing with this lemma they should identify
`vj = q` and `vk = p` (or equivalently apply `Orientation.oangle_rev` if the
opposite arg order is desired).

## A1 — Status and approach

The scoping report (`docs/97-arc-angle-parametrization-plan.md` §3, §5 A1)
proposed defining a 3-angle predicate `Real.Angle.btwArcNotThrough` and
formulating A1 as `OnArcOpposite vi vj vk v ↔ btwArcNotThrough …` on arc-angles
of `vj, vk, v` centered at the **MEC center**. The plan further claimed the iff
would reduce to `signedArea2_sign_eq_oangle_sign` + A0 alone, **without**
invoking the inscribed-angle theorem `Sphere.two_zsmul_oangle_eq`.

This dispatch confirms that the iff goes through with **no inscribed-angle
theorem and no cospherical / MEC-center hypothesis**, but the cleanest form does
not match the scoped predicate. The bridge
`signedArea2_sign_eq_oangle_sign` already returns an `Orientation.oangle`
*centered at the test point*, not at the MEC center. Applying A0
(`arcAngle_sub_arcAngle`) with `center := v` (and again with `center := vi`)
re-expresses each chord-vector `oangle` as a *difference* of arc-angles
centered at the test point itself. The resulting A1 statement is therefore a
sign equation on `arcAngle v · - arcAngle v ·` and `arcAngle vi · - arcAngle vi ·`,
*not* on `arcAngle center vi`, `arcAngle center vj`, `arcAngle center vk`,
`arcAngle center v` for a common `center`.

Concretely, A1 lands in two forms (a "core" oangle form, and an "arc-angle"
form by an immediate rewrite under A0):

```
onArcOpposite_iff_oangle_sign_mul :
  OnArcOpposite vi vj vk v ↔
    (stdOrientation.oangle (vj - v) (vk - v)).sign *
      (stdOrientation.oangle (vj - vi) (vk - vi)).sign ≤ 0

onArcOpposite_iff_arcAngle_sign_mul :
  OnArcOpposite vi vj vk v ↔
    (arcAngle v vk - arcAngle v vj).sign *
      (arcAngle vi vk - arcAngle vi vj).sign ≤ 0
```

Both require `vj ≠ v`, `vk ≠ v`, `vj ≠ vi`, `vk ≠ vi`. There is no MEC center,
no radius, and no cospherical hypothesis: A1 is a *purely chord-side* fact
about four points in the plane, with `arcAngle` serving as a notational
convenience for the inscribed-angle reading. Downstream consumers that want a
"common-center" form will need to fold in the inscribed-angle theorem
explicitly when they consume A1 — that step is **not** in A1's scope.

**Deviation from the scoping report.** The report's tentative
`btwArcNotThrough α β γ` 3-angle predicate is not used. After working through
the algebra, the predicate did not improve compositional clarity over the
direct sign-product form, and would have required either committing to a
common arc-center (forcing the inscribed-angle theorem) or duplicating the
sign-product statement under a wrapper. The wrapper-free form keeps A1 a one
`rw`-step composition of A0 and `signedArea2_sign_eq_oangle_sign`, with no new
predicates introduced.

## A2 — Status and approach

A2 establishes the **chord-length formula on a sphere**: for `p`, `q` both at
distance `r` from `center` (with `r > 0`), the Euclidean distance
`dist p q` equals `2 r · |sin((θ).toReal / 2)|` where
`θ = arcAngle center p - arcAngle center q`.

**Statement-shape deviation from the scoping report.** The plan (§S3, §5 A2)
proposed the canonical form

```
dist p q = 2 r · |Real.Angle.sin ((arcAngle center p - arcAngle center q) / 2)|
```

but `Real.Angle` has no `HDiv Real.Angle ℕ` instance — `θ / 2` is not
type-correct for `θ : Real.Angle`. The standard Mathlib idiom in this regime
is to lower the angle to its real representative via `Real.Angle.toReal`
(picking the unique lift in `(-π, π]`) and divide there:

```
dist p q = 2 r · |Real.sin ((arcAngle center p - arcAngle center q).toReal / 2)|
```

`|sin|` is invariant under `± 2π` shifts of its argument, so the choice of
`Real.Angle` lift does not affect the right-hand side. Downstream consumers
that prefer working entirely in `Real.Angle` can apply `Real.Angle.sin_toReal`
to convert between `Real.Angle.sin` and `Real.sin _.toReal` as needed, but the
formula on the angle quotient itself requires a packaged half-angle predicate
that Mathlib does not provide.

**Mathlib hook unavailable.** The plan flagged
`EuclideanGeometry.Sphere.dist_div_sin_oangle_div_two_eq_radius` as a possible
single-step closer, but that lemma takes three points all on the sphere
(`p₁, p₂, p₃ ∈ s`) and the angle is `oangle p₁ p₂ p₃` with the apex `p₂` *on*
the sphere — it is the *inscribed-angle* form. In A2 the apex is `center`,
which is **not** on the sphere. The lemma therefore does not apply; the proof
takes the plan's recommended polarization fallback.

**Proof sketch (polarization).** Let `u := p - center`, `v := q - center`, so
`‖u‖ = ‖v‖ = r`. Then

```
dist(p,q)² = ‖u - v‖²
           = ‖u‖² − 2⟪u, v⟫ + ‖v‖²        (norm_sub_sq_real)
           = 2r² − 2⟪u, v⟫
           = 2r² (1 − cos(oangle u v))    (inner_eq_norm_mul_norm_mul_cos_oangle)
           = 2r² (1 − cos(arcAngle p − arcAngle q))   (A0 + cos is even)
           = 4r² sin²((arcAngle p − arcAngle q).toReal / 2)   (half-angle)
           = (2r · |sin(…)|)²
```

The two sides are non-negative; squaring is injective on `[0, ∞)`
(`pow_left_inj₀`), so taking square roots closes the goal. Total proof ≈ 50
lines of straight-line algebra, no new axioms, no sorry. The cosine step needs
that `cos` on `Real.Angle` is symmetric (`Real.Angle.cos_neg`), which absorbs
the `oangle (q-center) (p-center)` vs `oangle (p-center) (q-center)` swap that
arises from A0's argument order.

The theorem `arcAngle_chord_length` is the headline export. Downstream
consumers (Lc1, Nivasch–Pach–Pinchasi–Zerbib L6, A3 monotonicity) read `dist p q` in terms of
`arcAngle` differences out of this lemma.

## A3 — Status and approach

A3 is the **strict monotonicity** of chord length in arc-angle difference. With
A2 in hand, the chord-length form reduces to the underlying analytic fact:

```
|θ₁.toReal| < |θ₂.toReal|  →  |sin(θ₁.toReal / 2)| < |sin(θ₂.toReal / 2)|
```

(for `θ₁, θ₂ : Real.Angle`). This file states both:

* `abs_sin_half_strict_mono` — the pure analytic statement above, decoupled
  from any geometric content. Useful in its own right (and reusable for any
  half-angle monotonicity argument on `Real.Angle`).
* `arcAngle_chord_length_strict_mono` — the chord-length form on a sphere: for
  `p, q₁, q₂` at distance `r > 0` from `center`, if the absolute arc-angle
  differences are strictly ordered (with `q₁` "closer" in arc angle), then the
  chord lengths are strictly ordered the same way.

**Proof key.** `Real.Angle.toReal` lands in `(-π, π]`, so the half `θ.toReal /
2` lands in `(-π/2, π/2]`. Inside this interval `|sin x| = sin |x|` (via
`Real.abs_sin_eq_sin_abs_of_abs_le_pi`), and `sin` is strictly monotone on
`[-π/2, π/2]` (via `Real.sin_lt_sin_of_lt_of_le_pi_div_two`). Combining these
gives strict monotonicity of `|sin(x/2)|` in `|x|` for `x ∈ (-π, π]`.

**Why we lift to `toReal`.** The scoping report (§5 A3) flagged risk
"`Real.Angle` arithmetic on the additive quotient". The cleanest avoidance is
to do all real-line monotonicity arguments after passing through
`Real.Angle.toReal`, exactly as in A2. No quotient arithmetic appears in the
A3 proofs — every step is on `ℝ` with `toReal` bounds supplied by
`Real.Angle.neg_pi_lt_toReal` and `Real.Angle.toReal_le_pi`.

**Deviation from the scoping report.** The report tentatively named the
analytic lemma `abs_sin_half_strict_mono` and the chord form
`arcAngle_chord_length_strict_mono`; both are retained. The hypothesis form is
`|θ₁.toReal| < |θ₂.toReal|` (rather than the report's symbolic
`0 ≤ |θ₁.toReal| < |θ₂.toReal| ≤ π`): the lower `0 ≤` is redundant (every
`abs` is non-negative) and the upper `≤ π` is automatic for any
`Real.Angle.toReal` value, so neither is a hypothesis. -/

open scoped EuclideanGeometry Real







/-- **Identity 2 — central subtraction bridge.** For `p, q` distinct from
`center`, the difference of arc-angles equals the oriented angle between the
two chord vectors. This is the load-bearing identity for the downstream A1/A2
/A3 program: it reduces every arc-angle subtraction to a single `oangle` on
chord vectors, where the existing `signedArea2_sign_eq_oangle_sign` bridge
applies.

**Argument order.** The right-hand side is `oangle (q - center) (p - center)`
(i.e. `q` first, `p` second), matching the direct consequence of
`Orientation.oangle_sub_left`. The reversed argument order can be recovered
via `Orientation.oangle_rev` at the cost of a sign flip.

**Nonzero hypotheses.** Both `p ≠ center` and `q ≠ center` are required: when
either chord vector is zero the right-hand side collapses to `0` via
`oangle_zero_*` while the left-hand side is generally nonzero. -/
theorem Problem97.arcAngle_sub_arcAngle (center p q : ℝ²)
    (hp : p ≠ center) (hq : q ≠ center) :
    arcAngle center p - arcAngle center q =
      stdOrientation.oangle (q - center) (p - center) := by
  unfold arcAngle
  have he : (EuclideanSpace.basisFun (Fin 2) ℝ) 0 ≠ (0 : ℝ²) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.ne_zero 0
  have hpv : p - center ≠ 0 := sub_ne_zero.mpr hp
  have hqv : q - center ≠ 0 := sub_ne_zero.mpr hq
  exact stdOrientation.oangle_sub_left he hqv hpv



/-- **Bridge 2 — center-apex signed area as an arc-angle difference sign.** With apex
at the center `c`, the sign of the signed twice-area `signedArea2 c a b` equals the sign
of the arc-angle difference `arcAngle c b − arcAngle c a` (note the swap: the *second*
point `b` comes first in the difference).

Proof: `signedArea2_sign_eq_oangle_sign c a b` rewrites the signed-area sign as the sign
of `oangle (a − c) (b − c)`; `arcAngle_sub_arcAngle c b a` (taking `p := b`, `q := a`)
identifies that with the sign of `arcAngle c b − arcAngle c a`.

Used by the §3.5 chord-side helper (`signedArea2_center_chord_clockwise`) to read the
chirality of a center-apex chord off the clockwise gap between two arc-angles. -/
theorem Problem97.signedArea2_center_sign_eq_arcAngle_sub_sign
    (c a b : ℝ²) (ha : a ≠ c) (hb : b ≠ c) :
    SignType.sign (signedArea2 c a b) = (arcAngle c b - arcAngle c a).sign := by
  rw [signedArea2_sign_eq_oangle_sign c a b ha hb, arcAngle_sub_arcAngle c b a hb ha]

/- ### A1 — `OnArcOpposite` ↔ sign-product bridge

`OnArcOpposite vi vj vk v` is the algebraic chord-separation predicate
`signedArea2 v vj vk * signedArea2 vi vj vk ≤ 0` (closed-cap convention).
Geometrically this says `v` and `vi` are on opposite (closed) sides of the
chord `vj`—`vk`.

Pushing the sign through `signedArea2_sign_eq_oangle_sign` (twice) rewrites
each `signedArea2` as the sign of an oriented angle on the two chord vectors,
centered at the corresponding test point. A further `rw` with
`arcAngle_sub_arcAngle` (taking the test point itself as the arc-angle
center) restates the bridge as a sign equation on differences of arc-angles
centered at the test points.

No MEC center, radius, or cospherical hypothesis is used — A1 is a purely
chord-side fact about four points in the plane. See the "A1 — Status and
approach" section in this file's module docstring for why this differs from
the scoping report's tentative 3-angle predicate. -/





/- ### A2 — chord-length formula on a sphere

For `p`, `q` both at distance `r > 0` from `center`, the Euclidean distance
`dist p q` equals `2 r |sin(θ/2)|` where `θ = arcAngle center p - arcAngle
center q`. See the "A2 — Status and approach" section in this file's module
docstring for the proof sketch (polarization) and for why the right-hand-side
half-angle is taken on `θ.toReal` rather than directly on `θ : Real.Angle`. -/



/- ### A3 — strict monotonicity of chord length in arc-angle difference

The chord-length formula A2 reads `dist p q = 2 r |sin(θ.toReal / 2)|` with
`θ = arcAngle center p - arcAngle center q`. To prove strict monotonicity of
the chord length in the arc-angle difference, the central analytic fact is

```
|θ₁.toReal| < |θ₂.toReal|  →  |sin(θ₁.toReal / 2)| < |sin(θ₂.toReal / 2)|
```

We package this as `abs_sin_half_strict_mono` (independent of geometry) and
then derive `arcAngle_chord_length_strict_mono` as a one-`rw` corollary using
A2. See the "A3 — Status and approach" section in this file's module
docstring for the proof key. -/





/- ### A3-iff — equality and `<` iff forms of strict monotonicity

The strict-monotonicity A3 (`arcAngle_chord_length_strict_mono`) is one
direction of an iff. For the Dumitrescu Lc1 witness-pair argument we also
need the **equality** direction: two MEC-arc points equidistant from a fixed
third MEC-arc point have arc-angle differences equal in absolute value
(arc-symmetry about the apex). With the analytic core
`abs_sin_half_eq_iff` in hand both directions of the chord-length comparison
collapse to comparisons on `|θ.toReal|`.

The four lemmas in this block come in two layers:

* **Analytic layer** — `abs_sin_half_eq_iff`, `abs_sin_half_lt_iff`. Pure
  half-angle sine facts on `Real.Angle.toReal`, decoupled from geometry. The
  equality form uses `Real.injOn_sin` on `[-π/2, π/2]`; the strict form is
  the iff lift of `abs_sin_half_strict_mono`.
* **Geometric layer** — `arcAngle_chord_length_eq_iff`,
  `arcAngle_chord_length_lt_iff`. Chord-length forms on a sphere, obtained
  by composing A2 (`arcAngle_chord_length`) with the analytic layer.

Together with `arcAngle_chord_length_strict_mono` (the `→` direction of
`_lt_iff`), the chord-length forms give a clean trichotomy: under
`p, q₁, q₂` all at distance `r` from `center`, the chord-length comparison
between `dist p q₁` and `dist p q₂` matches the comparison between
`|(arcAngle center p - arcAngle center q₁).toReal|` and
`|(arcAngle center p - arcAngle center q₂).toReal|` in all three cases
(`<`, `=`, `>`).

**Use in Dumitrescu Lc1.** The `CapWitnessRanking` constructor needs to
exhibit an injection from `capWitnessPairs A C` into a Finset of size
`|C| - 1`. Each witness pair `xy = {x, y} ⊆ C` carries an apex `a ∈ A \ C`
with `dist a x = dist a y`. Under the MEC-arc-membership hypothesis (cap
points all lie on the MEC, apex on or inside the MEC), the equality form
gives `|(arcAngle center a - arcAngle center x).toReal|
   = |(arcAngle center a - arcAngle center y).toReal|`, i.e. `x` and `y`
are arc-symmetric about the diameter through `a`. This is the geometric
input to the diagonal-vertex injection that realizes the `|C| - 1` bound. -/

end Erdos9796CountingFragment_Erdos9796Proof_P97_MEC_ArcAngle

section Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexCyclicOrder_Construct

open Problem97

/- Fragment from Erdos9796Proof.P97.ConvexCyclicOrder.Construct; source SHA-256 57dc74b4cc61e00d4333c450728c8f4df96124ae963c47fc084dbfa1f368bf19 -/



/-!
# ConvexCyclicOrder Step 2 — polar-sort construction (partial)

Constructive content toward `Problem97.exists_isCcwConvexPolygon_of_convexIndep`
(Step 2 of the ConvexCyclicOrder construction lane used by the CGN bridge).

Strategy (locked in `docs/97-convex-cyclic-order-step2-spec.md`): enumerate `A`
by angular order around an interior point `c` of `convexHull A`, using the
in-tree `Problem97.arcAngle c · : ℝ² → Real.Angle` and Mathlib's
`Real.Angle.instCircularOrder`, cutting the circular order open at an anchor.

This file currently lands the independent sub-lemmas and the geometric
injectivity sub-lemma:

* `exists_center_interior_convexHull_of_convexIndep_noncoll` (spec §3.1) — an
  interior point of `convexHull A` exists, from `¬ Collinear ⇒ affineSpan = ⊤`.
* `three_le_card_of_convexIndep_noncoll` (spec §3.6) — `¬ Collinear ⇒ 3 ≤ A.card`.
* `arcAngle_injective_of_center_interior` (spec §3.2) — for an interior center
  `c`, `arcAngle c ·` is injective on a convex-independent `A`. Distinct points
  on a common ray from `c` would force the nearer one to be an interior point of
  the hull, contradicting convex independence.

Supporting lemmas proved en route to §3.2:

* `notMem_extremePoints_of_mem_interior` — an interior point of any set in `ℝ²`
  is never an extreme point (midpoint-of-a-ball argument).
* `notMem_convexHull_diff_convexHull_of_notMem` — a Carathéodory/Hahn-Banach
  "descent": `a ∉ convexHull (A \ {a}) ⇒ a ∉ convexHull (convexHull A \ {a})`.
* `mem_extremePoints_of_convexIndep` — convex-independent points are extreme
  points of the hull.
* `notMem_interior_of_convexIndep` — convex-independent points are not interior
  to the hull.

It also lands the cut-open enumeration:

* `cutKey` (spec §3.3) — the cut-open linear key on `Real.Angle`, taken as
  `-Real.Angle.toReal` (anchor at `0`, i.e. the `+x` direction). It is globally
  injective because `toReal` is, which is all the *enumeration* lemma needs. The
  key is **negated** so that increasing `cutKey ∘ arcAngle c` walks the boundary
  *clockwise* in the standard orientation: a direct integer-coordinate check
  (recorded in `cutKey`'s docstring) shows this is the chirality
  `IsCcwConvexPolygon` requires (`(∡ ·)·.sign = 1`), whereas the
  counter-clockwise walk gives sign `-1`. This makes the enumeration directly
  consumable by the §3.5 geometric heart.
* `exists_cut_sorted_enumeration_of_convexIndep` (spec §3.4) — sort `A` by the
  cut-open key into `φ : Fin A.card → ℝ²`, strictly monotone in the key. Pure
  bookkeeping over `Finset.orderEmbOfFin` of the key-image, using §3.2 for
  injectivity of the key on `A`.

The remaining sub-lemma — §3.5, the geometric heart (cyclic angular order ⇒
CCW), and the final assembly — are **not** in this file yet; see
`docs/97-convex-cyclic-order-step2-spec.md` §3.5 and the risk register.
-/

open scoped EuclideanGeometry Real



/-! ### §3.6 — cardinality lower bound -/



/-! ### §3.1 — interior point of the convex hull -/





/-! ### Supporting helper — interior points are not extreme

An interior point of any set in `ℝ²` cannot be an extreme point: it is the
midpoint of two distinct nearby points of the set (obtained from a ball inside
the interior), so it is a non-trivial convex combination, contradicting the
extreme-point definition. -/



/-! ### §3.2 — `arcAngle` injective on `A` for an interior center

If `c` is interior to `convexHull A`, two distinct convex-independent points of
`A` cannot share a ray from `c`: the nearer one would be a strictly interior
point of the hull, contradicting convex independence. We package this through a
sequence of standard convexity facts: a Hahn-Banach "descent" lemma, the
extreme-point characterization of the hull, and the interior/extreme
incompatibility above. The injectivity statement lives on `Real.Angle` (not
`.toReal`), as required by the cut-open enumeration in §3.4. -/



/-- Convex-independent points of `A` are extreme points of `convexHull A`. This
is the extreme-point characterization
`Convex.mem_extremePoints_iff_mem_diff_convexHull_diff` applied to the convex set
`convexHull A`, with the descent lemma bridging the convex-hull-diff condition
from `A \ {a}` to `(convexHull A) \ {a}`. -/
theorem Problem97.mem_extremePoints_of_convexIndep {A : Finset ℝ²}
    (hA : Problem97.ConvexIndep A) {a : ℝ²} (ha : a ∈ A) :
    a ∈ Set.extremePoints ℝ (convexHull ℝ (A : Set ℝ²)) := by
  rw [Convex.mem_extremePoints_iff_mem_diff_convexHull_diff (convex_convexHull _ _)]
  refine ⟨subset_convexHull _ _ (by exact_mod_cast ha), ?_⟩
  exact notMem_convexHull_diff_convexHull_of_notMem ha (hA a (by exact_mod_cast ha))



/-- Convex-independent points of `A` are not interior to `convexHull A`:
they are extreme points (`mem_extremePoints_of_convexIndep`), and interior
points are never extreme (`notMem_extremePoints_of_mem_interior`). -/
theorem Problem97.notMem_interior_of_convexIndep {A : Finset ℝ²}
    (hA : Problem97.ConvexIndep A) {a : ℝ²} (ha : a ∈ A) :
    a ∉ interior (convexHull ℝ (A : Set ℝ²)) := fun hint =>
  notMem_extremePoints_of_mem_interior hint (mem_extremePoints_of_convexIndep hA ha)





/-! ### §3.3 / §3.4 — cut-open linear key and the sorted enumeration -/





/-- **Spec CGN4g-r3.** If the cut-open key is strictly monotone on the sorted
enumeration, then the real representatives of the intermediate vertices lie in
the long raw interval between the endpoints. -/
theorem Problem97.cut_sorted_intermediate_mem_long_gap
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    {i t k : Fin A.card} (hit : i < t) (htk : t < k)
    (hphi_sorted : StrictMono (fun i =>
      Problem97.cutKey (Problem97.arcAngle c (phi i)))) :
    (Problem97.arcAngle c (phi k)).toReal
      < (Problem97.arcAngle c (phi t)).toReal ∧
    (Problem97.arcAngle c (phi t)).toReal
      < (Problem97.arcAngle c (phi i)).toReal := by
  have hti : Problem97.cutKey (Problem97.arcAngle c (phi i))
      < Problem97.cutKey (Problem97.arcAngle c (phi t)) := hphi_sorted hit
  have htk' : Problem97.cutKey (Problem97.arcAngle c (phi t))
      < Problem97.cutKey (Problem97.arcAngle c (phi k)) := hphi_sorted htk
  simp [Problem97.cutKey] at hti htk'
  constructor <;> linarith

/-! ### §3.5 sub-lemma A — sign of an arc-angle difference from the clockwise gap

Two arc-angles `a, b : Real.Angle` differ by `b - a = ↑(b.toReal - a.toReal)`, whose
`Real.Angle.sign` is `SignType.sign (Real.sin (b.toReal - a.toReal))`. The cut-open key
`cutKey θ = -θ.toReal` is strictly increasing along the enumeration, so for `i < j` the
`toReal`s are strictly *decreasing*: `θ_j.toReal < θ_i.toReal`, i.e. the clockwise gap
`g := θ_j.toReal - θ_i.toReal` is negative. The sign of `(θ_j - θ_i)` is then governed by
whether the clockwise gap exceeds `π` in magnitude:

* `g ∈ (-π, 0)` (gap `< π`) ⇒ sign `-1`;
* `g ∈ (-2π, -π)` (gap `> π`) ⇒ sign `+1`. -/

/-- Sub-lemma A, short-gap branch: if `b.toReal - a.toReal ∈ (-π, 0)` then the angle
difference `b - a` has sign `-1`. -/
theorem Problem97.arcAngle_sub_sign_neg_of_gap_lt
    {a b : Real.Angle} (h1 : -π < b.toReal - a.toReal) (h2 : b.toReal - a.toReal < 0) :
    (b - a).sign = -1 := by
  have heq : b - a = ((b.toReal - a.toReal : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub, Real.Angle.coe_toReal, Real.Angle.coe_toReal]
  rw [heq, Real.Angle.sign, Real.Angle.sin_coe, sign_eq_neg_one_iff]
  exact Real.sin_neg_of_neg_of_neg_pi_lt h2 h1



/-! ### §3.5 sub-lemma C — a convex-independent triple is not collinear -/

  -- Wbtw z x y, middle x

/-! ### §3.5 sub-lemma B — interior center is "surrounded" by `A`

If `c` is interior to `convexHull A`, no closed half-plane through `c` contains all of `A`:
for every nonzero direction `u`, some `a ∈ A` has `⟪a - c, u⟫ < 0`. Proved by the §3.2
Hahn-Banach idiom in reverse — the closed half-space `{x | ⟪c,u⟫ ≤ ⟪x,u⟫}` is convex and
(if it contained all of `A`) would contain the whole hull, but a ball around the interior
point `c` pokes out of it in the `-u` direction. -/



/-! ### §3.5 sub-lemma D — center-apex chord chirality from the clockwise gap

Packages Bridge 2 (`signedArea2_center_sign_eq_arcAngle_sub_sign`) with sub-lemma A: the
center-apex signed area `signedArea2 c a b` is negative exactly when the clockwise gap
`arcAngle c b - arcAngle c a` is a "short" turn (its `toReal`-representative lies in
`(-π, 0)`), and positive on a "long" turn (`(-2π, -π)`). -/

/-- **Spec §3.5 sub-lemma D, short-gap branch.** If the `toReal`-gap of the arc-angles is
in `(-π, 0)`, the center-apex signed area `signedArea2 c a b` is negative. -/
theorem Problem97.signedArea2_center_chord_clockwise {c a b : ℝ²} (ha : a ≠ c) (hb : b ≠ c)
    (h1 : -π < (arcAngle c b).toReal - (arcAngle c a).toReal)
    (h2 : (arcAngle c b).toReal - (arcAngle c a).toReal < 0) :
    signedArea2 c a b < 0 := by
  have hsign : (arcAngle c b - arcAngle c a).sign = -1 :=
    arcAngle_sub_sign_neg_of_gap_lt h1 h2
  have hbridge := signedArea2_center_sign_eq_arcAngle_sub_sign c a b ha hb
  rw [hsign] at hbridge
  rwa [sign_eq_neg_one_iff] at hbridge



/-! ### CGN4g radial-chord helper stack -/


































theorem solution
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    (hA : Problem97.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    (_hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    (hphi_sorted : StrictMono (fun i => Problem97.cutKey
      (Problem97.arcAngle c (phi i))))
    {i j k : Fin A.card} (hij : i < j) (hjk : j < k)
    (hgap : (Problem97.arcAngle c (phi k)).toReal
      - (Problem97.arcAngle c (phi i)).toReal = -Real.pi) :
    Problem97.signedArea2 (phi i) (phi j) (phi k) < 0 := by
  have hik : i < k := lt_trans hij hjk
  have hiA : phi i ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hjA : phi j ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have hkA : phi k ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  have hic : phi i ≠ c := by
    intro h
    subst h
    exact Problem97.notMem_interior_of_convexIndep hA hiA hc
  have hjc : phi j ≠ c := by
    intro h
    subst h
    exact Problem97.notMem_interior_of_convexIndep hA hjA hc
  have hkc : phi k ≠ c := by
    intro h
    subst h
    exact Problem97.notMem_interior_of_convexIndep hA hkA hc
  have hcseg : c ∈ openSegment ℝ (phi i) (phi k) :=
    Problem97.center_mem_openSegment_of_arcAngle_gap_eq_neg_pi hic hkc hgap
  rw [openSegment_eq_image_lineMap] at hcseg
  obtain ⟨r, hrIoo, hc_line⟩ := hcseg
  have hinterval := Problem97.cut_sorted_intermediate_mem_long_gap hij hjk hphi_sorted
  have hjgap1 : -Real.pi < (Problem97.arcAngle c (phi j)).toReal
      - (Problem97.arcAngle c (phi i)).toReal := by
    linarith [hinterval.1, hgap]
  have hjgap2 : (Problem97.arcAngle c (phi j)).toReal
      - (Problem97.arcAngle c (phi i)).toReal < 0 := by
    linarith [hinterval.2]
  have hcenter_neg : Problem97.signedArea2 c (phi i) (phi j) < 0 :=
    Problem97.signedArea2_center_chord_clockwise hic hjc hjgap1 hjgap2
  have hcyc_neg : Problem97.signedArea2 (phi i) (phi j) c < 0 := by
    have hcyc : Problem97.signedArea2 (phi i) (phi j) c =
        Problem97.signedArea2 c (phi i) (phi j) := by
      simp [Problem97.signedArea2]
      ring
    rw [hcyc]
    exact hcenter_neg
  have hscale : Problem97.signedArea2 (phi i) (phi j) c =
      r * Problem97.signedArea2 (phi i) (phi j) (phi k) := by
    rw [← hc_line]
    simp [Problem97.signedArea2, AffineMap.lineMap_apply_module']
    ring
  have hscaled : r * Problem97.signedArea2 (phi i) (phi j) (phi k) < 0 := by
    simpa [hscale] using hcyc_neg
  have hrpos : 0 < r := hrIoo.1
  nlinarith

end Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexCyclicOrder_Construct
