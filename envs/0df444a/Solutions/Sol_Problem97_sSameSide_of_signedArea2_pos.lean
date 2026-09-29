-- Prove2me | solution 1 for Problem97.sSameSide_of_signedArea2_pos
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:07:03.405354+00:00
-- url     : https://prove2.me/submissions/e89fe230-e942-444d-a115-1bb99ade4d63

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.ConvexCyclicOrder.Construct:50757:56453. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_SignedAreaOangle
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.Finset.Sort
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Theorems.Thm_Problem97_collinear_of_signedArea2_eq_zero

section Erdos9796CountingFragment_Erdos9796Proof_P97_SignedAreaOangle

open Problem97

/- Fragment from Erdos9796Proof.P97.SignedAreaOangle; source SHA-256 b3d7d5da8bb313997dd505e15b0ba2823db075ab8d863e995246ecbcce8f4fa9 -/


/-!
# Bridge: algebraic `signedArea2` ↔ Mathlib oriented angle sign

This module supplies the foundational bridge consumed by the MEC arc–angle
chain (sub-obligation `p97-signed-area-eq-oangle-sign`, alias A.1). The
algebraic predicate `Problem97.signedArea2` defined in `Foundation` is the
chord-side / signed-area form used by the cap-witness machinery. The MEC
parametrization, in contrast, needs Mathlib's oriented angle
`Orientation.oangle` on the standard counter-clockwise orientation of
`ℝ² = EuclideanSpace ℝ (Fin 2)`. Both quantities carry the *same sign* by a
direct computation: `signedArea2` is exactly the area form of the standard
orientation evaluated on the two chord vectors, and `oangle` is the
`Complex.arg` of the Kähler form whose imaginary part is that area form.

The single externally-used result is `signedArea2_sign_eq_oangle_sign`
(plus its `Real.sign` cast variant). All proofs are by direct Mathlib
manipulation; no new axioms are introduced.
-/

open scoped EuclideanGeometry





/-- The algebraic `signedArea2` is exactly the area form of the standard
orientation evaluated on the chord vectors `vj - v` and `vk - v`. -/
theorem Problem97.signedArea2_eq_stdOrientation_areaForm (v vj vk : ℝ²) :
    Problem97.signedArea2 v vj vk =
      stdOrientation.areaForm (vj - v) (vk - v) := by
  rw [stdOrientation, Orientation.areaForm_to_volumeForm,
      Orientation.volumeForm_robust _ (EuclideanSpace.basisFun (Fin 2) ℝ) rfl,
      Module.Basis.det_apply]
  simp only [Module.Basis.toMatrix_apply, Matrix.det_fin_two, signedArea2,
             EuclideanSpace.basisFun_toBasis, PiLp.basisFun_repr,
             Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.sub_apply]

end Erdos9796CountingFragment_Erdos9796Proof_P97_SignedAreaOangle

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





















set_option maxHeartbeats 1000000 in
-- Basis expansion plus the affine-side witness construction is elaboration-heavy.

theorem solution
    {a b x y : ℝ²}
    (hab : a ≠ b)
    (hx : 0 < Problem97.signedArea2 a b x)
    (hy : 0 < Problem97.signedArea2 a b y) :
    line[ℝ, a, b].SSameSide x y := by
  let u : ℝ² := b - a
  have hu : u ≠ 0 := by
    dsimp [u]
    simpa using sub_ne_zero.mpr hab.symm
  let β := Problem97.stdOrientation.basisRightAngleRotation u hu
  let sx : ℝ := β.repr (x - a) 0
  let tx : ℝ := β.repr (x - a) 1
  let sy : ℝ := β.repr (y - a) 0
  let ty : ℝ := β.repr (y - a) 1
  have hsumx := β.sum_repr (x - a)
  have hsumy := β.sum_repr (y - a)
  have hdecompx : x - a = sx • u + tx • Problem97.stdOrientation.rightAngleRotation u := by
    simpa [β, u, sx, tx] using hsumx.symm
  have hdecompy : y - a = sy • u + ty • Problem97.stdOrientation.rightAngleRotation u := by
    simpa [β, u, sy, ty] using hsumy.symm
  have hx' : x = a + sx • u + tx • Problem97.stdOrientation.rightAngleRotation u := by
    have := congrArg (fun z : ℝ² => z + a) hdecompx
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hy' : y = a + sy • u + ty • Problem97.stdOrientation.rightAngleRotation u := by
    have := congrArg (fun z : ℝ² => z + a) hdecompy
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hsmul_left : ∀ r : ℝ, Problem97.stdOrientation.areaForm u (r • u) = 0 := by
    intro r
    rw [map_smul]
    simp
  have hsmul_right : ∀ r : ℝ,
      Problem97.stdOrientation.areaForm u (r • Problem97.stdOrientation.rightAngleRotation u)
        = r * ‖u‖ ^ 2 := by
    intro r
    rw [map_smul]
    simp [Orientation.areaForm_rightAngleRotation_right]
  have hxarea : Problem97.signedArea2 a b x = tx * ‖u‖ ^ 2 := by
    calc
      Problem97.signedArea2 a b x = Problem97.stdOrientation.areaForm u (x - a) := by
        rw [Problem97.signedArea2_eq_stdOrientation_areaForm]
      _ = Problem97.stdOrientation.areaForm u
          (sx • u + tx • Problem97.stdOrientation.rightAngleRotation u) := by
        rw [hdecompx]
      _ = tx * ‖u‖ ^ 2 := by
        rw [map_add, hsmul_left sx, hsmul_right tx]
        simp
  have hyarea : Problem97.signedArea2 a b y = ty * ‖u‖ ^ 2 := by
    calc
      Problem97.signedArea2 a b y = Problem97.stdOrientation.areaForm u (y - a) := by
        rw [Problem97.signedArea2_eq_stdOrientation_areaForm]
      _ = Problem97.stdOrientation.areaForm u
          (sy • u + ty • Problem97.stdOrientation.rightAngleRotation u) := by
        rw [hdecompy]
      _ = ty * ‖u‖ ^ 2 := by
        rw [map_add, hsmul_left sy, hsmul_right ty]
        simp
  have hsqpos : 0 < ‖u‖ ^ 2 := by
    have hnormne : ‖u‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hu
    exact sq_pos_of_ne_zero hnormne
  have htxpos : 0 < tx := by
    exact pos_of_mul_pos_left (by simpa [hxarea] using hx) (le_of_lt hsqpos)
  have htypos : 0 < ty := by
    exact pos_of_mul_pos_left (by simpa [hyarea] using hy) (le_of_lt hsqpos)
  have htxne : tx ≠ 0 := ne_of_gt htxpos
  have hratio : 0 < ty / tx := div_pos htypos htxpos
  have hline_area_zero : ∀ {z : ℝ²}, z ∈ line[ℝ, a, b] →
      Problem97.signedArea2 a b z = 0 := by
    intro z hzline
    obtain ⟨r, hr⟩ :=
      (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ)
        (p := z) (p₁ := a) (p₂ := b)).mp hzline
    rw [← hr]
    unfold Problem97.signedArea2
    simp [AffineMap.lineMap_apply_module']
    ring
  have hxnot : x ∉ line[ℝ, a, b] := by
    intro hxline
    have hzero : Problem97.signedArea2 a b x = 0 := hline_area_zero hxline
    rw [hzero] at hx
    exact (lt_irrefl (0 : ℝ)) hx
  have hynot : y ∉ line[ℝ, a, b] := by
    intro hyline
    have hzero : Problem97.signedArea2 a b y = 0 := hline_area_zero hyline
    rw [hzero] at hy
    exact (lt_irrefl (0 : ℝ)) hy
  let p2 : ℝ² := y - (ty / tx) • (x - a)
  have hvec : y -ᵥ p2 = (ty / tx) • (x -ᵥ a) := by
    dsimp [p2]
    module
  have hp2area : Problem97.signedArea2 a b p2 = 0 := by
    calc
      Problem97.signedArea2 a b p2 =
          Problem97.stdOrientation.areaForm u (p2 - a) := by
        rw [Problem97.signedArea2_eq_stdOrientation_areaForm]
      _ = Problem97.stdOrientation.areaForm u
          ((y - a) - (ty / tx) • (x - a)) := by
        dsimp [p2]
        congr 1
        module
      _ = Problem97.stdOrientation.areaForm u (y - a)
          - (ty / tx) * Problem97.stdOrientation.areaForm u (x - a) := by
        simp [map_sub, map_smul]
      _ = Problem97.signedArea2 a b y
          - (ty / tx) * Problem97.signedArea2 a b x := by
        rw [Problem97.signedArea2_eq_stdOrientation_areaForm]
        rw [Problem97.signedArea2_eq_stdOrientation_areaForm]
      _ = 0 := by
        rw [hyarea, hxarea]
        field_simp [htxne]
        ring
  have hp2 : p2 ∈ line[ℝ, a, b] := by
    have hcol : Collinear ℝ ({a, b, p2} : Set ℝ²) :=
      Problem97.collinear_of_signedArea2_eq_zero a b p2 hp2area
    exact hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab
  refine (AffineSubspace.sSameSide_iff_exists_left (s := line[ℝ, a, b]) (x := x) (y := y)
      (p₁ := a) (left_mem_affineSpan_pair ℝ a b)).2 ?_
  have hsray : SameRay ℝ (x - a) ((ty / tx) • (x - a)) :=
    SameRay.sameRay_pos_smul_right (R := ℝ) (M := ℝ²) (S := ℝ) (a := ty / tx)
      (v := x - a) hratio
  exact ⟨hxnot, hynot, ⟨p2, hp2, by
    rw [hvec]
    exact hsray⟩⟩

end Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexCyclicOrder_Construct
