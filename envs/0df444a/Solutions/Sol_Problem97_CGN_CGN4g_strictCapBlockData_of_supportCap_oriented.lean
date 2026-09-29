-- Prove2me | solution 1 for Problem97.CGN.CGN4g_strictCapBlockData_of_supportCap_oriented
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:07:26.084668+00:00
-- url     : https://prove2.me/submissions/72bf1835-d84c-45ed-aa83-b362902510ea

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN4g:61969:78727. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN4g
import Definitions.Def_Erdos9796Counting_Cap_Structure
import Definitions.Def_Erdos9796Counting_CircumscribedMECPacket
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
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Theorems.Thm_Problem97_CGN_CGN4g1_capBlock_of_supportCap
import Theorems.Thm_Problem97_CGN_CGN4g2_consecutiveTurn_nonpos_of_capBlock
import Theorems.Thm_Problem97_ConvexIndep_not_wbtw
import Theorems.Thm_Problem97_affineSpan_eq_top_of_not_collinear
import Theorems.Thm_Problem97_boundaryBlock_openSide_iff_between_indices_of_signedAreaOrder
import Theorems.Thm_Problem97_boundaryCap_chordProjection_strict
import Theorems.Thm_Problem97_ccw_of_hneg
import Theorems.Thm_Problem97_center_same_side_as_apex_of_nonobtuse
import Theorems.Thm_Problem97_exists_cut_sorted_enumeration_of_convexIndep
import Theorems.Thm_Problem97_hneg_cyclicShift
import Theorems.Thm_Problem97_hneg_of_ccw
import Theorems.Thm_Problem97_isCcwConvexPolygon_of_cut_sorted_arcAngle
import Theorems.Thm_Problem97_signedArea2_eq_zero_iff_collinear
import Theorems.Thm_Problem97_signedArea2_sign_eq_oangle_sign
import Theorems.Thm_Problem97_three_le_card_of_convexIndep_noncoll

section Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexCyclicOrder_Basic

open Problem97

/- Fragment from Erdos9796Proof.P97.ConvexCyclicOrder.Basic; source SHA-256 f1ec282e547e3f3ca8edca05b96111ec2591b61f6aeecd11c668396d093955a1 -/



/-!
# Convex cyclic order wrapper around `IsCcwConvexPolygon`

This module supplies a thin wrapper around the upstream predicate
`EuclideanGeometry.IsCcwConvexPolygon` (from
`FormalConjecturesForMathlib.Geometry.2d`) suited to the Nivasch–Pach–Pinchasi–Zerbib 2013
Lemma 6 sign-stability arguments consumed downstream by the CGN counting
bridge.

The key downstream consumer needs the statement "four points
`p, q, r, s` appear in this cyclic order on the convex-hull boundary
of `A`" plus an immediate algebraic API:

* `Problem97.ConvexCyclicOrder A p q r s` — the wrapper predicate.
* `oangle_sign_{pqr,qrs,pqs,prs}` — direct sign extraction for the
  four oriented angles whose central vertex is in the interior of
  the index sequence (immediate from `IsCcwConvexPolygon.sign_oangle`).
* `signedArea2_sign_stable_{pq, qr_chord}` — sign-stability of the
  `signedArea2` predicate as the third/first point varies along the
  cyclic order. Bridges via `signedArea2_sign_eq_oangle_sign` in
  `SignedAreaOangle`.

All proofs are mechanical composition of `IsCcwConvexPolygon.sign_oangle*`
with `signedArea2_sign_eq_oangle_sign`. No axioms are introduced.

## Step 1 scope

This file is the Step 1 wrapper.  It now includes the generic cyclic-shift
transport for `IsCcwConvexPolygon`, enough to change the linear cut of a
global boundary enumeration.  The higher-level
`ConvexCyclicOrder.rotate`/`ConvexCyclicOrder.reverse` wrapper API is still
deferred to Step 2.  Reversal flips chirality, so a faithful Step-2 reverse
should wrap upstream `IsConvexPolygon` (which already handles both
chiralities) rather than `IsCcwConvexPolygon`.
-/

open scoped EuclideanGeometry













/-- A cyclic shift of a CCW convex-polygon enumeration is CCW. -/
theorem Problem97.isCcwConvexPolygon_cyclicShift {n : ℕ} {φ : Fin n → ℝ²}
    (hinj : Function.Injective φ)
    (hccw : EuclideanGeometry.IsCcwConvexPolygon φ) (cut : Fin n) :
    EuclideanGeometry.IsCcwConvexPolygon (fun t : Fin n => φ (t + cut)) := by
  have hneg : ∀ {i j k : Fin n}, i < j → j < k →
      signedArea2 (φ i) (φ j) (φ k) < 0 :=
    fun {_ _ _} hij hjk => hneg_of_ccw hinj hccw hij hjk
  have hneg_s : ∀ {i j k : Fin n}, i < j → j < k →
      signedArea2 (φ (i + cut)) (φ (j + cut)) (φ (k + cut)) < 0 :=
    fun {_ _ _} hij hjk => hneg_cyclicShift hneg cut hij hjk
  have hinj_s : Function.Injective (fun t : Fin n => φ (t + cut)) := by
    intro a b h
    exact add_left_injective cut (hinj h)
  exact ccw_of_hneg hinj_s (fun {i j k} hij hjk => hneg_s hij hjk)







-- TODO Step 2: ConvexCyclicOrder.rotate — `ConvexCyclicOrder A p q r s
-- → ConvexCyclicOrder A q r s p`. The generic boundary-enumeration cyclic
-- shift above supplies the geometric transport; the remaining work is a
-- wrapper-level theorem that repacks the four witnesses.
--
-- TODO Step 2: ConvexCyclicOrder.reverse — reversing the cyclic order
-- flips CCW → CW. The faithful Step-2 form should be stated over
-- `IsConvexPolygon` (the chirality-agnostic predicate at
-- `FormalConjecturesForMathlib/Geometry/2d.lean`), not the CCW form.

/-! ### Direct oriented-angle sign extraction

For each triple `(x, y, z) ⊆ {p, q, r, s}` whose central vertex `y` is
in the *middle* of the cyclic index sequence, `IsCcwConvexPolygon.sign_oangle`
directly yields `(∡ x y z).sign = 1`. The four such triples are listed
below.
-/









/-! ### `signedArea2` sign-stability

Bridge the oriented-angle extraction above to the algebraic
`signedArea2` predicate via `Problem97.signedArea2_sign_eq_oangle_sign`.
Recall the convention `signedArea2 v vj vk ↔ ∡ vj v vk` (central vertex
is the *first* argument of `signedArea2`).
-/

end Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexCyclicOrder_Basic

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



/-- **Spec §3.1.** A convex-independent, non-collinear finite set in `ℝ²` has a
point in the topological interior of its convex hull. Proof: non-collinearity
forces `affineSpan A = ⊤`, and in finite dimensions a set spanning the whole
affine space has convex hull with nonempty interior
(`interior_convexHull_nonempty_iff_affineSpan_eq_top`). -/
theorem Problem97.exists_center_interior_convexHull_of_convexIndep_noncoll
    {A : Finset ℝ²} (_hA : Problem97.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²)) :
    ∃ c : ℝ², c ∈ interior (convexHull ℝ (A : Set ℝ²)) := by
  have hspan : affineSpan ℝ (A : Set ℝ²) = ⊤ :=
    affineSpan_eq_top_of_not_collinear hnoncoll
  have hint : (interior (convexHull ℝ (A : Set ℝ²))).Nonempty :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  exact hint

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









































/-- **Step 2 wrapper.** Every convex-independent non-collinear finite set in
`ℝ²` admits a global CCW convex-boundary enumeration. -/
theorem Problem97.exists_isCcwConvexPolygon_of_convexIndep
    {A : Finset ℝ²} (hA : Problem97.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²)) :
    ∃ (n : ℕ) (_ : 3 ≤ n) (phi : Fin n → ℝ²),
      Function.Injective phi ∧
      Finset.univ.image phi = A ∧
      EuclideanGeometry.IsCcwConvexPolygon phi := by
  obtain ⟨c, hc⟩ := Problem97.exists_center_interior_convexHull_of_convexIndep_noncoll hA hnoncoll
  obtain ⟨phi, hphi_inj, hphi_image, hphi_sorted⟩ :=
    Problem97.exists_cut_sorted_enumeration_of_convexIndep hA hc
  refine ⟨A.card, Problem97.three_le_card_of_convexIndep_noncoll hA hnoncoll, phi,
    hphi_inj, hphi_image, ?_⟩
  exact Problem97.isCcwConvexPolygon_of_cut_sorted_arcAngle
    hA hc hphi_inj hphi_image hphi_sorted

end Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexCyclicOrder_Construct

section Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexIndepHelpers

open Problem97 Problem97.ConvexIndep

/- Fragment from Erdos9796Proof.P97.ConvexIndepHelpers; source SHA-256 58fea6fdfc458ff582e9e12c324d10b6e51a5653a6daa5dc80f586642be49129 -/


/-!
# `ConvexIndep` Finset helpers (Milestone 2)

Direct proofs from the extreme-point characterization
`EuclideanGeometry.ConvexIndep S ↔ ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})`:

* `ConvexIndep.mono` — `B ⊆ A → ConvexIndep A → ConvexIndep B`
* `ConvexIndep.erase` — `ConvexIndep A → ConvexIndep (A.erase x)`

These power the M4 descent step: erasing a removable vertex from a
counterexample preserves convex independence, and more generally any
subset of a convex-independent set is convex independent.
-/

open scoped EuclideanGeometry







/-- CGN2a: three collinear points have a weakly-between middle point. -/
theorem Problem97.collinear_three_wbtw {x y z : ℝ²}
    (hcol : Collinear ℝ ({x, y, z} : Set ℝ²)) :
    Wbtw ℝ x y z ∨ Wbtw ℝ y z x ∨ Wbtw ℝ z x y := by
  simpa using hcol.wbtw_or_wbtw_or_wbtw



/-- CGN5b: no line contains three distinct points of a convex-independent
finite set. -/
theorem Problem97.ConvexIndep.not_three_collinear {A : Finset ℝ²}
    (hA : ConvexIndep A) {x y z : ℝ²} (hx : x ∈ A) (hy : y ∈ A)
    (hz : z ∈ A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hcol : Collinear ℝ ({x, y, z} : Set ℝ²)) : False := by
  rcases collinear_three_wbtw hcol with hw | hw | hw
  · exact hA.not_wbtw hx hy hz hw hxy.symm hyz
  · exact hA.not_wbtw hy hz hx hw hyz.symm hxz.symm
  · exact hA.not_wbtw hz hx hy hw hxz hxy

end Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexIndepHelpers

section Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN4g

open Problem97 Problem97.CGN

/- Fragment from Erdos9796Proof.P97.CGN.CGN4g; source SHA-256 c412b95ca627805e0db3a1f0d192f80b93891249e4eb1369844d4f8206dcba79 -/


/-!
# CGN4g: ordered-cap block packaging

This file adds the closure-plan data carrier for the ordered-cap block cut out
of a global convex-boundary enumeration, together with the theorem wrappers
that are pure packaging.

The geometric producers for the block (`CGN4g1`, `CGN4g3`, `CGN4g4`) remain
separate. The declarations here are the sanctioned interfaces consumed by the
existing CGN6 / CGN7 layers.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace




/-- `CGN4g0`: re-export the global convex-boundary order wrapper under the
CGN-local name consumed by the cap-block extractor. -/
theorem Problem97.CGN.CGN4g0_globalBoundaryOrder_of_convexIndep
    {A : Finset ℝ²} (hA : Problem97.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²)) :
    ∃ (n : ℕ) (_ : 3 ≤ n) (phi : Fin n → ℝ²),
      Function.Injective phi ∧
      Finset.univ.image phi = A ∧
      EuclideanGeometry.IsCcwConvexPolygon phi := by
  simpa using Problem97.exists_isCcwConvexPolygon_of_convexIndep hA hnoncoll







variable {A C : Finset ℝ²}





































/-- Local CGN4g helper: once the omitted support vertex is the cut point of
the global boundary order, the opposite support cap is exactly the closed
interval between the two support endpoints. This is not a new public CGN
interface; it packages the `CapTriple.arc_membership` predicate as a finite
interval statement so it can feed `CGN4g1_capBlock_of_supportCap`. -/
 theorem Problem97.CGN.supportCap_interval_of_oppositeFirst
    {A C : Finset ℝ²} {n : ℕ} {phi : Fin n → ℝ²}
    {u v w : ℝ²}
    (_hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi i) (phi j) (phi k) < 0)
    (hC_subset : C ⊆ A)
    (hC_arc : ∀ x ∈ A, x ∈ C ↔ Problem97.OnArcOpposite u v w x)
    (hv_mem : v ∈ C)
    (hw_mem : w ∈ C)
    {u_idx v_idx w_idx : Fin n}
    (hu : phi u_idx = u)
    (hv : phi v_idx = v)
    (hw : phi w_idx = w)
    (huv : u_idx < v_idx)
    (hvw : v_idx < w_idx) :
    ∀ x : ℝ², x ∈ C ↔ ∃ q : Fin n, v_idx ≤ q ∧ q ≤ w_idx ∧ phi q = x := by
  have huw : u_idx < w_idx := lt_trans huv hvw
  have hu_neg : Problem97.signedArea2 u v w < 0 := by
    simpa [hu, hv, hw] using hneg huv hvw
  intro x
  constructor
  · intro hxC
    have hxA : x ∈ A := hC_subset hxC
    rw [← hphi_image] at hxA
    rcases Finset.mem_image.mp hxA with ⟨q, _, rfl⟩
    have hqA : phi q ∈ A := by
      rw [← hphi_image]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ q)
    have hq_arc : Problem97.OnArcOpposite u v w (phi q) :=
      (hC_arc (phi q) hqA).1 hxC
    have hnot_lt_left : ¬ q < v_idx := by
      intro hqv
      have hq_neg : Problem97.signedArea2 (phi q) v w < 0 := by
        simpa [hv, hw] using hneg hqv hvw
      have hprod_pos : 0 <
          Problem97.signedArea2 (phi q) v w * Problem97.signedArea2 u v w := by
        have h1 : 0 < -Problem97.signedArea2 (phi q) v w := by linarith
        have h2 : 0 < -Problem97.signedArea2 u v w := by linarith
        have hpos : 0 < (-Problem97.signedArea2 (phi q) v w) *
            (-Problem97.signedArea2 u v w) := by positivity
        simpa [neg_mul_neg] using hpos
      unfold Problem97.OnArcOpposite at hq_arc
      linarith
    have hnot_lt_right : ¬ w_idx < q := by
      intro hwq
      have hq_neg_vwx : Problem97.signedArea2 v w (phi q) < 0 := by
        simpa [hv, hw] using hneg hvw hwq
      have hcyc : Problem97.signedArea2 (phi q) v w =
          Problem97.signedArea2 v w (phi q) := by
        simp [Problem97.signedArea2]
        ring
      have hq_neg : Problem97.signedArea2 (phi q) v w < 0 := by
        rw [hcyc]
        exact hq_neg_vwx
      have hprod_pos : 0 <
          Problem97.signedArea2 (phi q) v w * Problem97.signedArea2 u v w := by
        have h1 : 0 < -Problem97.signedArea2 (phi q) v w := by linarith
        have h2 : 0 < -Problem97.signedArea2 u v w := by linarith
        have hpos : 0 < (-Problem97.signedArea2 (phi q) v w) *
            (-Problem97.signedArea2 u v w) := by positivity
        simpa [neg_mul_neg] using hpos
      unfold Problem97.OnArcOpposite at hq_arc
      linarith
    exact ⟨q, le_of_not_gt hnot_lt_left, le_of_not_gt hnot_lt_right, rfl⟩
  · rintro ⟨q, hvle, hqle, rfl⟩
    have hqA : phi q ∈ A := by
      rw [← hphi_image]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ q)
    rcases eq_or_lt_of_le hvle with rfl | hvq
    · simpa [hv] using hv_mem
    rcases eq_or_lt_of_le hqle with rfl | hqw
    · simpa [hw] using hw_mem
    · have hmid_neg : Problem97.signedArea2 v (phi q) w < 0 := by
        simpa [hv, hw] using hneg hvq hqw
      have hcyc : Problem97.signedArea2 (phi q) v w =
          Problem97.signedArea2 v w (phi q) := by
        simp [Problem97.signedArea2]
        ring
      have hswap : Problem97.signedArea2 v w (phi q) =
          -Problem97.signedArea2 v (phi q) w := by
        simp [Problem97.signedArea2]
      have hq_pos : 0 < Problem97.signedArea2 (phi q) v w := by
        rw [hcyc, hswap]
        linarith
      have hq_arc : Problem97.OnArcOpposite u v w (phi q) := by
        unfold Problem97.OnArcOpposite
        have hprod_nonpos :
            Problem97.signedArea2 (phi q) v w * Problem97.signedArea2 u v w ≤ 0 := by
          nlinarith
        exact hprod_nonpos
      exact (hC_arc (phi q) hqA).2 hq_arc

/-- Local CGN4g helper: strict negative signed-area order on increasing
triples is preserved under cyclic shifts of the boundary enumeration.  This is
the finite-order bookkeeping behind "cut the global order at the omitted
support vertex" before applying
`supportCap_interval_of_oppositeFirst`. -/
 theorem Problem97.CGN.hneg_of_cyclicShift
    {n : ℕ} {phi : Fin n → ℝ²}
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi i) (phi j) (phi k) < 0)
    (cut : Fin n) :
    ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi (i + cut)) (phi (j + cut)) (phi (k + cut)) < 0 := by
  have hcyc {a b c : ℝ²} :
      Problem97.signedArea2 a b c = Problem97.signedArea2 c a b := by
    simp [Problem97.signedArea2]
    ring
  let bound : ℕ := n - cut.val
  have hval_nowrap {t : Fin n} (ht : (t : ℕ) < bound) :
      ((t + cut : Fin n) : ℕ) = t.val + cut.val := by
    rw [Fin.val_add_eq_ite]
    have hlt : ¬ n ≤ t.val + cut.val := by
      omega
    simp [hlt]
  have hval_wrap {t : Fin n} (ht : bound ≤ (t : ℕ)) :
      ((t + cut : Fin n) : ℕ) = t.val - bound := by
    rw [Fin.val_add_eq_ite]
    have hge : n ≤ t.val + cut.val := by
      omega
    simp [hge]
    omega
  intro i j k hij hjk
  have hik : i < k := lt_trans hij hjk
  by_cases hk : (k : ℕ) < bound
  · have hi : (i : ℕ) < bound := by omega
    have hj : (j : ℕ) < bound := by omega
    have hij' : i + cut < j + cut := by
      change (((i + cut : Fin n) : ℕ) < ((j + cut : Fin n) : ℕ))
      rw [hval_nowrap hi, hval_nowrap hj]
      omega
    have hjk' : j + cut < k + cut := by
      change (((j + cut : Fin n) : ℕ) < ((k + cut : Fin n) : ℕ))
      rw [hval_nowrap hj, hval_nowrap hk]
      omega
    exact hneg hij' hjk'
  · by_cases hj : (j : ℕ) < bound
    · have hi : (i : ℕ) < bound := by omega
      have hk' : bound ≤ (k : ℕ) := by omega
      have hki : k + cut < i + cut := by
        change (((k + cut : Fin n) : ℕ) < ((i + cut : Fin n) : ℕ))
        rw [hval_wrap hk', hval_nowrap hi]
        omega
      have hij' : i + cut < j + cut := by
        change (((i + cut : Fin n) : ℕ) < ((j + cut : Fin n) : ℕ))
        rw [hval_nowrap hi, hval_nowrap hj]
        omega
      have hneg' :
          Problem97.signedArea2 (phi (k + cut)) (phi (i + cut)) (phi (j + cut)) < 0 :=
        hneg hki hij'
      simpa [hcyc] using hneg'
    · by_cases hi : (i : ℕ) < bound
      · have hj' : bound ≤ (j : ℕ) := by omega
        have hk' : bound ≤ (k : ℕ) := by omega
        have hjk'' : j + cut < k + cut := by
          change (((j + cut : Fin n) : ℕ) < ((k + cut : Fin n) : ℕ))
          rw [hval_wrap hj', hval_wrap hk']
          omega
        have hki : k + cut < i + cut := by
          change (((k + cut : Fin n) : ℕ) < ((i + cut : Fin n) : ℕ))
          rw [hval_wrap hk', hval_nowrap hi]
          omega
        have hneg' :
            Problem97.signedArea2 (phi (j + cut)) (phi (k + cut)) (phi (i + cut)) < 0 :=
          hneg hjk'' hki
        simpa [hcyc] using hneg'
      · have hi' : bound ≤ (i : ℕ) := by omega
        have hj' : bound ≤ (j : ℕ) := by omega
        have hk' : bound ≤ (k : ℕ) := by omega
        have hij' : i + cut < j + cut := by
          change (((i + cut : Fin n) : ℕ) < ((j + cut : Fin n) : ℕ))
          rw [hval_wrap hi', hval_wrap hj']
          omega
        have hjk' : j + cut < k + cut := by
          change (((j + cut : Fin n) : ℕ) < ((k + cut : Fin n) : ℕ))
          rw [hval_wrap hj', hval_wrap hk']
          omega
        exact hneg hij' hjk'













/-- `CGN4g3`: package strict endpoint-chord projection order from the global
signed-area boundary order and the MEC-side packet fields. -/
theorem Problem97.CGN.CGN4g3_chordProjection_strict_of_capBlock
    {A C : Finset ℝ²} {n m : ℕ}
    {phi : Fin n → ℝ²} {L : OrderedCap m}
    (hA : Problem97.ConvexIndep A)
    (Block : BoundaryCapBlock A C phi L)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi i) (phi j) (phi k) < 0)
    (Packet : MecCapPacket A L)
    (Hside : MinorCapSideHypotheses Packet) :
    ∀ {r s : Fin m}, r < s ->
      0 < inner ℝ (L.points s - L.points r)
        (L.points (lastIndex Packet.hm) - L.points (firstIndex Packet.hm)) := by
  intro r s hrs
  simpa using Problem97.boundaryCap_chordProjection_strict
    (A := A) (C := C) (phi := phi) (L := L) hA Block hneg Packet Hside hrs

/-- `CGN4g4`: package the local subchord open-side characterization from the
global signed-area order helper. -/
theorem Problem97.CGN.CGN4g4_subchord_open_side_iff_A_of_capBlock
    {A C : Finset ℝ²} {n m : ℕ}
    {phi : Fin n → ℝ²} {L : OrderedCap m}
    (Block : BoundaryCapBlock A C phi L)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi i) (phi j) (phi k) < 0)
    (hno3 : ∀ {x y z : ℝ²}, x ∈ A → y ∈ A → z ∈ A →
      x ≠ y → y ≠ z → x ≠ z →
      Problem97.signedArea2 x y z ≠ 0) :
    ∀ {r s : Fin m}, r < s → ∀ {x : ℝ²}, x ∈ A →
      (0 < Problem97.signedArea2 (L.points r) (L.points s) x ↔
        ∃ j : Fin m, r < j ∧ j < s ∧ L.points j = x) := by
  intro r s hrs x hxA
  simpa using Problem97.boundaryBlock_openSide_iff_between_indices_of_signedAreaOrder
    (Block := Block) (hneg := hneg) (_hno3 := hno3) (r := r) (s := s) hrs (x := x) hxA

/-- `CGN4g5`: assemble the pure packaging fields into the public strict cap
order interface consumed by CGN6 / CGN7. -/
theorem Problem97.CGN.CGN4g5_strictCapOrder_of_capBlock
    {A C : Finset ℝ²} {n m : ℕ}
    {phi : Fin n → ℝ²} {L : OrderedCap m}
    (Block : BoundaryCapBlock A C phi L)
    (hturn : ∀ t : ℕ, ∀ ht : t + 2 < m,
      Problem97.signedArea2
        (L.points ⟨t, by
          exact lt_trans
            (Nat.lt_add_of_pos_right (by decide : 0 < (2 : ℕ))) ht⟩)
        (L.points ⟨t + 1, by
          exact lt_trans
            (Nat.succ_lt_succ (Nat.lt_add_of_pos_right (by decide : 0 < (1 : ℕ))))
            ht⟩)
        (L.points ⟨t + 2, by
          exact ht⟩) ≤ 0)
    (hproj : ∀ {r s : Fin m}, r < s →
      0 < inner ℝ (L.points s - L.points r)
        (L.points (lastIndex Block.hm) - L.points (firstIndex Block.hm)))
    (hsideiff : ∀ {r s : Fin m}, r < s → ∀ {x : ℝ²}, x ∈ A →
      (0 < Problem97.signedArea2 (L.points r) (L.points s) x ↔
        ∃ j : Fin m, r < j ∧ j < s ∧ L.points j = x)) :
    StrictCapOrder A L where
  hm := Block.hm
  consecutive_turn_nonpos := hturn
  chord_projection_strict := by
    intro i j hij
    simpa using hproj hij
  subchord_open_side_iff_A := hsideiff


theorem solution
    {A C : Finset ℝ²} {M : Problem97.MoserTriangle A}
    (hA : Problem97.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²))
    (hC_subset : C ⊆ A)
    (hC_arc : ∀ x ∈ A, x ∈ C ↔ Problem97.OnArcOpposite M.v1 M.v2 M.v3 x)
    (hv_mem : M.v2 ∈ C)
    (hw_mem : M.v3 ∈ C)
    (P : Problem97.CircumscribedMECPacket A M)
    (hacute : 0 ≤ ⟪M.v2 - M.v1, M.v3 - M.v1⟫_ℝ) :
    ∃ B : StrictCapBlockData A C,
      (B.L.points (firstIndex B.Packet.hm) = M.v2 ∧
          B.L.points (lastIndex B.Packet.hm) = M.v3) ∨
        (B.L.points (firstIndex B.Packet.hm) = M.v3 ∧
          B.L.points (lastIndex B.Packet.hm) = M.v2) := by
  classical
  obtain ⟨n, hn, phi, hphi_inj, hphi_image, hccw⟩ :=
    CGN4g0_globalBoundaryOrder_of_convexIndep hA hnoncoll
  haveI : NeZero n := ⟨by omega⟩
  have hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi i) (phi j) (phi k) < 0 := by
    intro i j k hij hjk
    have hij_ne : phi i ≠ phi j := by
      intro h
      exact (ne_of_lt hij) (hphi_inj h)
    have hkj_ne : phi k ≠ phi j := by
      intro h
      exact (ne_of_gt hjk) (hphi_inj h)
    have hswap : Problem97.signedArea2 (phi j) (phi i) (phi k) =
        -Problem97.signedArea2 (phi i) (phi j) (phi k) := by
      simp [Problem97.signedArea2]
      ring
    have hsign : SignType.sign (Problem97.signedArea2 (phi j) (phi i) (phi k)) = 1 := by
      rw [Problem97.signedArea2_sign_eq_oangle_sign (phi j) (phi i) (phi k) hij_ne hkj_ne]
      exact hccw.sign_oangle hij hjk
    have hpos : 0 < Problem97.signedArea2 (phi j) (phi i) (phi k) := (sign_eq_one_iff).mp hsign
    linarith
  have hv1A : M.v1 ∈ Finset.univ.image phi := by
    rw [hphi_image]
    exact M.v1_mem
  have hv2A : M.v2 ∈ Finset.univ.image phi := by
    rw [hphi_image]
    exact M.v2_mem
  have hv3A : M.v3 ∈ Finset.univ.image phi := by
    rw [hphi_image]
    exact M.v3_mem
  rcases Finset.mem_image.mp hv1A with ⟨i1, _, hi1⟩
  rcases Finset.mem_image.mp hv2A with ⟨i2, _, hi2⟩
  rcases Finset.mem_image.mp hv3A with ⟨i3, _, hi3⟩
  let psi : Fin n → ℝ² := fun t => phi (t + i1)
  have hpsi_inj : Function.Injective psi := by
    intro a b hab
    apply (finCycle i1).injective
    exact hphi_inj hab
  have hpsi_image : Finset.univ.image psi = A := by
    calc
      Finset.univ.image psi = Finset.univ.image (fun t : Fin n => phi (t + i1)) := rfl
      _ = Finset.univ.image phi := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨t, _, rfl⟩
          exact Finset.mem_image_of_mem phi (Finset.mem_univ _)
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨q, _, rfl⟩
          refine Finset.mem_image.mpr ?_
          refine ⟨q - i1, Finset.mem_univ _, ?_⟩
          rw [show (q - i1) + i1 = q by
            simpa [finCycle] using (Equiv.apply_symm_apply (finCycle i1) q)]
      _ = A := hphi_image
  have hpsi_ccw : EuclideanGeometry.IsCcwConvexPolygon psi := by
    exact isCcwConvexPolygon_cyclicShift hphi_inj hccw i1
  have hneg_shift :
      ∀ {i j k : Fin n}, i < j → j < k →
        Problem97.signedArea2 (psi i) (psi j) (psi k) < 0 := by
    intro i j k hij hjk
    simpa [psi] using
      (Problem97.CGN.hneg_of_cyclicShift (phi := phi) hneg i1 hij hjk :
        Problem97.signedArea2 (phi (i + i1)) (phi (j + i1)) (phi (k + i1)) < 0)
  have hpsi0 : psi 0 = M.v1 := by
    change phi (0 + i1) = M.v1
    simpa [psi, hi1] using hi1
  have hi2_ne_i1 : i2 ≠ i1 := by
    intro h
    exact M.v12_ne (by simpa [hi1, hi2] using (congrArg phi h).symm)
  have hi3_ne_i1 : i3 ≠ i1 := by
    intro h
    exact M.v13_ne (by simpa [hi1, hi3] using (congrArg phi h).symm)
  have hi2_ne_i3 : i2 ≠ i3 := by
    intro h
    exact M.v23_ne (by simpa [hi2, hi3] using congrArg phi h)
  have hi2_pos : 0 < i2 - i1 := by
    exact Fin.pos_iff_ne_zero.mpr (by
      intro h0
      apply hi2_ne_i1
      have h := congrArg (fun t : Fin n => t + i1) h0
      simpa [finCycle] using h)
  have hi3_pos : 0 < i3 - i1 := by
    exact Fin.pos_iff_ne_zero.mpr (by
      intro h0
      apply hi3_ne_i1
      have h := congrArg (fun t : Fin n => t + i1) h0
      simpa [finCycle] using h)
  by_cases h23 : i2 - i1 < i3 - i1
  · have hC_interval :
        ∀ x : ℝ², x ∈ C ↔
          ∃ q : Fin n, i2 - i1 ≤ q ∧ q ≤ i3 - i1 ∧ psi q = x := by
      simpa [psi, hi1, hi2, hi3] using
        Problem97.CGN.supportCap_interval_of_oppositeFirst
          (A := A) (C := C) (phi := psi)
          hpsi_inj hpsi_image hneg_shift hC_subset hC_arc hv_mem hw_mem
          (u_idx := 0) (v_idx := i2 - i1) (w_idx := i3 - i1)
          hpsi0 (by simpa [psi, hi2] using hi2) (by simpa [psi, hi3] using hi3)
          hi2_pos h23
    have hcap_side :
        ∀ x, x ∈ C →
          0 ≤ Problem97.signedArea2 (psi (i2 - i1)) (psi (i3 - i1)) x := by
      intro x hxC
      rcases (hC_interval x).1 hxC with ⟨q, hqlo, hqhi, rfl⟩
      rcases eq_or_lt_of_le hqlo with rfl | hqlo'
      · simp [Problem97.signedArea2]
      rcases eq_or_lt_of_le hqhi with rfl | hqhi'
      · simp [Problem97.signedArea2]
      · have hneg_mid :
          Problem97.signedArea2 (psi (i2 - i1)) (psi q) (psi (i3 - i1)) < 0 := by
          exact hneg_shift hqlo' hqhi'
        have hswap :
            Problem97.signedArea2 (psi (i2 - i1)) (psi (i3 - i1)) (psi q) =
              -Problem97.signedArea2 (psi (i2 - i1)) (psi q) (psi (i3 - i1)) := by
          simp [Problem97.signedArea2]
        rw [hswap]
        linarith
    have hcenter_prod :
        0 ≤ Problem97.signedArea2 P.center (psi (i2 - i1)) (psi (i3 - i1)) *
          Problem97.signedArea2 (psi 0) (psi (i2 - i1)) (psi (i3 - i1)) := by
      have hacuteψ :
          0 ≤ ⟪psi (i2 - i1) - psi 0, psi (i3 - i1) - psi 0⟫_ℝ := by
        simpa [psi, hpsi0, hi2, hi3] using hacute
      have h := Problem97.center_same_side_as_apex_of_nonobtuse
        (O := P.center) (a := psi (i2 - i1)) (b := psi (i3 - i1)) (c := psi 0)
        (r := P.radius)
        (by simpa [psi, hi2] using P.moser_on_boundary_2)
        (by simpa [psi, hi3] using P.moser_on_boundary_3)
        (by simpa [hpsi0] using P.moser_on_boundary_1)
        hacuteψ
      simpa [mul_comm] using h
    have hcenter_neg :
        Problem97.signedArea2 (psi (i2 - i1)) (psi (i3 - i1)) P.center ≤ 0 := by
      have hbase_neg :
          Problem97.signedArea2 (psi 0) (psi (i2 - i1)) (psi (i3 - i1)) < 0 :=
        hneg_shift hi2_pos h23
      have hcyc :
          Problem97.signedArea2 P.center (psi (i2 - i1)) (psi (i3 - i1)) =
            Problem97.signedArea2 (psi (i2 - i1)) (psi (i3 - i1)) P.center := by
        simp [Problem97.signedArea2]
        ring
      rw [hcyc] at hcenter_prod
      by_contra hpos
      push_neg at hpos
      have : Problem97.signedArea2 (psi (i2 - i1)) (psi (i3 - i1)) P.center *
          Problem97.signedArea2 (psi 0) (psi (i2 - i1)) (psi (i3 - i1)) < 0 :=
        mul_neg_of_pos_of_neg hpos hbase_neg
      linarith
    obtain ⟨m, L, Packet, Hside, Block, hlo, hhi⟩ :=
      CGN4g1_capBlock_of_supportCap
        (A := A) (C := C) (phi := psi)
        hpsi_inj hpsi_image h23 hC_interval
        P.center P.radius (le_of_lt P.radius_pos)
        (fun x hx => P.disk_contains_A x (hC_subset hx))
        (by simpa [psi, hi2, dist_eq_norm] using P.moser_on_boundary_2)
        (by simpa [psi, hi3, dist_eq_norm] using P.moser_on_boundary_3)
        hcap_side hcenter_neg
    have hturn := CGN4g2_consecutiveTurn_nonpos_of_capBlock Block hneg_shift
    have hproj :
        ∀ {r s : Fin m}, r < s →
          0 < inner ℝ (L.points s - L.points r)
            (L.points (lastIndex Packet.hm) - L.points (firstIndex Packet.hm)) := by
      intro r s hrs
      exact CGN4g3_chordProjection_strict_of_capBlock
        (A := A) (C := C) (phi := psi) (L := L) hA Block hneg_shift Packet Hside hrs
    have hno3 :
        ∀ {x y z : ℝ²}, x ∈ A → y ∈ A → z ∈ A →
          x ≠ y → y ≠ z → x ≠ z →
          Problem97.signedArea2 x y z ≠ 0 := by
      intro x y z hx hy hz hxy hyz hxz hzero
      have hcol : Collinear ℝ ({x, y, z} : Set ℝ²) :=
        (Problem97.signedArea2_eq_zero_iff_collinear x y z).1 hzero
      exact False.elim (Problem97.ConvexIndep.not_three_collinear hA hx hy hz hxy hxz hyz hcol)
    have hsideiff :
        ∀ {r s : Fin m}, r < s → ∀ {x : ℝ²}, x ∈ A →
          (0 < Problem97.signedArea2 (L.points r) (L.points s) x ↔
            ∃ j : Fin m, r < j ∧ j < s ∧ L.points j = x) := by
      intro r s hrs
      exact fun {x} hx => by
        simpa using
          (CGN4g4_subchord_open_side_iff_A_of_capBlock
            (A := A) (C := C) (phi := psi) (L := L)
            Block hneg_shift hno3 (r := r) (s := s) hrs (x := x) hx)
    let Hord : StrictCapOrder A L :=
      CGN4g5_strictCapOrder_of_capBlock Block hturn hproj hsideiff
    have hfirst_v2 : L.points (firstIndex Packet.hm) = M.v2 := by
      calc
        L.points (firstIndex Packet.hm)
            = psi (Block.idx (firstIndex Packet.hm)) := by
                exact Block.points_eq (firstIndex Packet.hm)
        _ = psi Block.lo := by rw [Block.idx_first]
        _ = psi (i2 - i1) := by rw [hlo]
        _ = M.v2 := by simpa [psi, hi2] using hi2
    have hlast_v3 : L.points (lastIndex Packet.hm) = M.v3 := by
      calc
        L.points (lastIndex Packet.hm)
            = psi (Block.idx (lastIndex Packet.hm)) := by
                exact Block.points_eq (lastIndex Packet.hm)
        _ = psi Block.hi := by rw [Block.idx_last]
        _ = psi (i3 - i1) := by rw [hhi]
        _ = M.v3 := by simpa [psi, hi3] using hi3
    let B : StrictCapBlockData A C := {
      n := n
      m := m
      phi := psi
      phi_injective := hpsi_inj
      phi_ccw := hpsi_ccw
      L := L
      Packet := Packet
      Hside := Hside
      Block := Block
      Hord := Hord
    }
    exact ⟨B, Or.inl ⟨hfirst_v2, hlast_v3⟩⟩
  · have h32 : i3 - i1 < i2 - i1 := lt_of_le_of_ne (le_of_not_gt h23) (by
        intro hEq
        exact hi2_ne_i3 (by
          have h := congrArg (fun t : Fin n => t + i1) hEq
          simpa [finCycle] using h.symm))
    have hswap_arc :
        ∀ x ∈ A, x ∈ C ↔ Problem97.OnArcOpposite M.v1 M.v3 M.v2 x := by
      intro x hxA
      rw [hC_arc x hxA]
      unfold Problem97.OnArcOpposite
      have hx :
          Problem97.signedArea2 x M.v3 M.v2 = -Problem97.signedArea2 x M.v2 M.v3 := by
        simp [Problem97.signedArea2]
      have hu :
          Problem97.signedArea2 M.v1 M.v3 M.v2 = -Problem97.signedArea2 M.v1 M.v2 M.v3 := by
        simp [Problem97.signedArea2]
      rw [hx, hu, neg_mul_neg]
    have hacute' : 0 ≤ ⟪M.v3 - M.v1, M.v2 - M.v1⟫_ℝ := by
      simpa [real_inner_comm] using hacute
    have hC_interval :
        ∀ x : ℝ², x ∈ C ↔
          ∃ q : Fin n, i3 - i1 ≤ q ∧ q ≤ i2 - i1 ∧ psi q = x := by
      simpa [psi, hi1, hi2, hi3] using
        Problem97.CGN.supportCap_interval_of_oppositeFirst
          (A := A) (C := C) (phi := psi)
          hpsi_inj hpsi_image hneg_shift hC_subset hswap_arc hw_mem hv_mem
          (u_idx := 0) (v_idx := i3 - i1) (w_idx := i2 - i1)
          hpsi0 (by simpa [psi, hi3] using hi3) (by simpa [psi, hi2] using hi2)
          hi3_pos h32
    have hcap_side :
        ∀ x, x ∈ C →
          0 ≤ Problem97.signedArea2 (psi (i3 - i1)) (psi (i2 - i1)) x := by
      intro x hxC
      rcases (hC_interval x).1 hxC with ⟨q, hqlo, hqhi, rfl⟩
      rcases eq_or_lt_of_le hqlo with rfl | hqlo'
      · simp [Problem97.signedArea2]
      rcases eq_or_lt_of_le hqhi with rfl | hqhi'
      · simp [Problem97.signedArea2]
      · have hneg_mid :
          Problem97.signedArea2 (psi (i3 - i1)) (psi q) (psi (i2 - i1)) < 0 := by
          exact hneg_shift hqlo' hqhi'
        have hswap :
            Problem97.signedArea2 (psi (i3 - i1)) (psi (i2 - i1)) (psi q) =
              -Problem97.signedArea2 (psi (i3 - i1)) (psi q) (psi (i2 - i1)) := by
          simp [Problem97.signedArea2]
        rw [hswap]
        linarith
    have hcenter_prod :
        0 ≤ Problem97.signedArea2 P.center (psi (i3 - i1)) (psi (i2 - i1)) *
          Problem97.signedArea2 (psi 0) (psi (i3 - i1)) (psi (i2 - i1)) := by
      have hacuteψ :
          0 ≤ ⟪psi (i3 - i1) - psi 0, psi (i2 - i1) - psi 0⟫_ℝ := by
        simpa [psi, hpsi0, hi2, hi3, real_inner_comm] using hacute'
      have h := Problem97.center_same_side_as_apex_of_nonobtuse
        (O := P.center) (a := psi (i3 - i1)) (b := psi (i2 - i1)) (c := psi 0)
        (r := P.radius)
        (by simpa [psi, hi3] using P.moser_on_boundary_3)
        (by simpa [psi, hi2] using P.moser_on_boundary_2)
        (by simpa [hpsi0] using P.moser_on_boundary_1)
        hacuteψ
      simpa [mul_comm] using h
    have hcenter_neg :
        Problem97.signedArea2 (psi (i3 - i1)) (psi (i2 - i1)) P.center ≤ 0 := by
      have hbase_neg :
          Problem97.signedArea2 (psi 0) (psi (i3 - i1)) (psi (i2 - i1)) < 0 :=
        hneg_shift hi3_pos h32
      have hcyc :
          Problem97.signedArea2 P.center (psi (i3 - i1)) (psi (i2 - i1)) =
            Problem97.signedArea2 (psi (i3 - i1)) (psi (i2 - i1)) P.center := by
        simp [Problem97.signedArea2]
        ring
      rw [hcyc] at hcenter_prod
      by_contra hpos
      push_neg at hpos
      have : Problem97.signedArea2 (psi (i3 - i1)) (psi (i2 - i1)) P.center *
          Problem97.signedArea2 (psi 0) (psi (i3 - i1)) (psi (i2 - i1)) < 0 :=
        mul_neg_of_pos_of_neg hpos hbase_neg
      linarith
    obtain ⟨m, L, Packet, Hside, Block, hlo, hhi⟩ :=
      CGN4g1_capBlock_of_supportCap
        (A := A) (C := C) (phi := psi)
        hpsi_inj hpsi_image h32 hC_interval
        P.center P.radius (le_of_lt P.radius_pos)
        (fun x hx => P.disk_contains_A x (hC_subset hx))
        (by simpa [psi, hi3, dist_eq_norm] using P.moser_on_boundary_3)
        (by simpa [psi, hi2, dist_eq_norm] using P.moser_on_boundary_2)
        hcap_side hcenter_neg
    have hturn := CGN4g2_consecutiveTurn_nonpos_of_capBlock Block hneg_shift
    have hproj :
        ∀ {r s : Fin m}, r < s →
          0 < inner ℝ (L.points s - L.points r)
            (L.points (lastIndex Packet.hm) - L.points (firstIndex Packet.hm)) := by
      intro r s hrs
      exact CGN4g3_chordProjection_strict_of_capBlock
        (A := A) (C := C) (phi := psi) (L := L) hA Block hneg_shift Packet Hside hrs
    have hno3 :
        ∀ {x y z : ℝ²}, x ∈ A → y ∈ A → z ∈ A →
          x ≠ y → y ≠ z → x ≠ z →
          Problem97.signedArea2 x y z ≠ 0 := by
      intro x y z hx hy hz hxy hyz hxz hzero
      have hcol : Collinear ℝ ({x, y, z} : Set ℝ²) :=
        (Problem97.signedArea2_eq_zero_iff_collinear x y z).1 hzero
      exact False.elim (Problem97.ConvexIndep.not_three_collinear hA hx hy hz hxy hxz hyz hcol)
    have hsideiff :
        ∀ {r s : Fin m}, r < s → ∀ {x : ℝ²}, x ∈ A →
          (0 < Problem97.signedArea2 (L.points r) (L.points s) x ↔
            ∃ j : Fin m, r < j ∧ j < s ∧ L.points j = x) := by
      intro r s hrs
      exact fun {x} hx => by
        simpa using
          (CGN4g4_subchord_open_side_iff_A_of_capBlock
            (A := A) (C := C) (phi := psi) (L := L)
            Block hneg_shift hno3 (r := r) (s := s) hrs (x := x) hx)
    let Hord : StrictCapOrder A L :=
      CGN4g5_strictCapOrder_of_capBlock Block hturn hproj hsideiff
    have hfirst_v3 : L.points (firstIndex Packet.hm) = M.v3 := by
      calc
        L.points (firstIndex Packet.hm)
            = psi (Block.idx (firstIndex Packet.hm)) := by
                exact Block.points_eq (firstIndex Packet.hm)
        _ = psi Block.lo := by rw [Block.idx_first]
        _ = psi (i3 - i1) := by rw [hlo]
        _ = M.v3 := by simpa [psi, hi3] using hi3
    have hlast_v2 : L.points (lastIndex Packet.hm) = M.v2 := by
      calc
        L.points (lastIndex Packet.hm)
            = psi (Block.idx (lastIndex Packet.hm)) := by
                exact Block.points_eq (lastIndex Packet.hm)
        _ = psi Block.hi := by rw [Block.idx_last]
        _ = psi (i2 - i1) := by rw [hhi]
        _ = M.v2 := by simpa [psi, hi2] using hi2
    let B : StrictCapBlockData A C := {
      n := n
      m := m
      phi := psi
      phi_injective := hpsi_inj
      phi_ccw := hpsi_ccw
      L := L
      Packet := Packet
      Hside := Hside
      Block := Block
      Hord := Hord
    }
    exact ⟨B, Or.inr ⟨hfirst_v3, hlast_v2⟩⟩

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN4g
