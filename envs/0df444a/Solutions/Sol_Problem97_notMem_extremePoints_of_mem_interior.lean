-- Prove2me | solution 1 for Problem97.notMem_extremePoints_of_mem_interior
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:05.319657+00:00
-- url     : https://prove2.me/submissions/2e149867-5d97-4b9a-ad03-11c8eb6b71eb

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.ConvexCyclicOrder.Construct:6674:8103. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.Finset.Sort

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


theorem solution
    {s : Set ℝ²} {a : ℝ²} (ha : a ∈ interior s) :
    a ∉ Set.extremePoints ℝ s := by
  rw [mem_extremePoints]
  push_neg
  intro _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior a ha
  set v : ℝ² := (ε / 2) • (EuclideanSpace.basisFun (Fin 2) ℝ) 0 with hv
  have hbase_ne : (EuclideanSpace.basisFun (Fin 2) ℝ) 0 ≠ (0 : ℝ²) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.ne_zero 0
  have hbase_norm : ‖(EuclideanSpace.basisFun (Fin 2) ℝ) 0‖ = 1 :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.1 0
  have hvne : v ≠ 0 := by
    rw [hv]; exact smul_ne_zero (by positivity) hbase_ne
  have hvnorm : ‖v‖ = ε / 2 := by
    rw [hv, norm_smul, hbase_norm, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hmem₁ : a + v ∈ s := by
    apply interior_subset; apply hball
    rw [Metric.mem_ball, dist_self_add_left, hvnorm]; linarith
  have hmem₂ : a - v ∈ s := by
    apply interior_subset; apply hball
    rw [Metric.mem_ball, dist_self_sub_left, hvnorm]; linarith
  refine ⟨a + v, hmem₁, a - v, hmem₂, ?_, ?_⟩
  · exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
  · intro _ hcontra
    apply hvne
    have : a - v = a := hcontra
    rwa [sub_eq_self] at this

/-! ### §3.2 — `arcAngle` injective on `A` for an interior center

If `c` is interior to `convexHull A`, two distinct convex-independent points of
`A` cannot share a ray from `c`: the nearer one would be a strictly interior
point of the hull, contradicting convex independence. We package this through a
sequence of standard convexity facts: a Hahn-Banach "descent" lemma, the
extreme-point characterization of the hull, and the interior/extreme
incompatibility above. The injectivity statement lives on `Real.Angle` (not
`.toReal`), as required by the cut-open enumeration in §3.4. -/













/-! ### §3.3 / §3.4 — cut-open linear key and the sorted enumeration -/







/-! ### §3.5 sub-lemma A — sign of an arc-angle difference from the clockwise gap

Two arc-angles `a, b : Real.Angle` differ by `b - a = ↑(b.toReal - a.toReal)`, whose
`Real.Angle.sign` is `SignType.sign (Real.sin (b.toReal - a.toReal))`. The cut-open key
`cutKey θ = -θ.toReal` is strictly increasing along the enumeration, so for `i < j` the
`toReal`s are strictly *decreasing*: `θ_j.toReal < θ_i.toReal`, i.e. the clockwise gap
`g := θ_j.toReal - θ_i.toReal` is negative. The sign of `(θ_j - θ_i)` is then governed by
whether the clockwise gap exceeds `π` in magnitude:

* `g ∈ (-π, 0)` (gap `< π`) ⇒ sign `-1`;
* `g ∈ (-2π, -π)` (gap `> π`) ⇒ sign `+1`. -/





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





/-! ### CGN4g radial-chord helper stack -/

end Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexCyclicOrder_Construct
