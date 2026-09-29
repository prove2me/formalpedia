-- Prove2me | solution 1 for Problem97.Dumitrescu.three_cap_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:07:14.602833+00:00
-- url     : https://prove2.me/submissions/a397dfb0-a050-42c5-b0e8-029d1fb6c91e

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.Dumitrescu.L4:2382:4784. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Cap_PartitionFromMEC
import Definitions.Def_Erdos9796Counting_Cap_Structure
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Definitions.Def_Erdos9796Counting_Moser_Triangle
import Theorems.Thm_Problem97_MEC_arc_partition_count_eq_one
import Theorems.Thm_Problem97_MEC_cap_partition_from_moser_circumscribed
import Theorems.Thm_Problem97_MEC_not_collinear_of_three_dist_eq
import Theorems.Thm_Problem97_cap_sum_identity
import Theorems.Thm_Problem97_collinear_of_signedArea2_eq_zero

section Erdos9796CountingFragment_Erdos9796Proof_P97_Cap_Structure

open Problem97 Problem97.CapTriple

/- Fragment from Erdos9796Proof.P97.Cap.Structure; source SHA-256 c37032098ca734b3732823b68f086b864f33a605fab97f4d15fc1010f9faeb11 -/


/-!
# Cap-structural packet: Moser triangle, cap triple, surplus cap data

This file is the *structural data layer* used by the U1–U7 surplus-cap
program (see `docs/97-uniform-theorem-closure-plan.md`).  The closure
plan talks freely about

* a minimum-enclosing-circle (MEC) and a *Moser triangle* — three MEC
  boundary vertices `v1, v2, v3 ∈ A`;
* the *three closed caps* `C1, C2, C3` they cut on the convex polygon
  `A` (each `Ci` is the closed chain between `v_{i+1}` and `v_{i+2}`
  not passing through `v_i`, *including* the two endpoints);
* a *surplus cap*: one of the `Ci` with `|Ci| > 4`;
* the regime `(m, 4, 4)`: two caps of size exactly `4` and one cap
  of size `m ≥ 5`.

Mathlib has no general-purpose minimum-enclosing-circle / Moser-cap
infrastructure.  This file does **not** attempt to build that
infrastructure.  Instead it packages exactly the **abstract
combinatorial data** that the U1 prose reduces to, so that downstream
formal arguments can consume the packet without re-deriving its
geometric provenance.  In the "structure-first" pattern flagged on the
blueprint obligation `p97-mec-setup`, this is the structure half;
existence of the data on a real counterexample is a separate
obligation that will eventually instantiate the packet.

Every definition here is purely about `Finset ℝ²` cardinalities,
membership, and the existing `ConvexIndep` / `HasNEquidistantProperty`
predicates.  No geometric content (MEC center, radius, Apollonius
arcs) is asserted at this layer — those data only enter at the
existence step, and at the geometric sub-lemmas of U1.

We use the **closed-cap convention** matching the existing
combinatorial `Problem97.CapPartition` in `CapPartition.lean`: each cap `Ci`
includes its two adjacent Moser-vertex endpoints, so adjacent caps
share an endpoint, every Moser vertex sits in exactly two caps, and
every non-Moser vertex sits in exactly one cap.  The cap-sum identity
in this convention reads

  `|C1| + |C2| + |C3| = |A| + 3`,

which is the identity already proved on `CapPartition`.

## Main definitions

* `Problem97.MoserTriangle A` — a labelled triple of distinct vertices
  of `A`.
* `Problem97.CapTriple A M` — a labelled triple of subsets of `A` in
  the closed-cap convention: each cap contains the two non-opposite
  Moser vertices, caps cover `A`, and every non-Moser vertex lies in
  exactly one cap.
## Main lemmas (PROVEN)

* `CapTriple.toCapPartition` — convert a geometric `CapTriple` to the
  abstract `CapPartition` of `CapPartition.lean`, where the cap-sum
  identity is already proved.
* `CapTriple.cap_sum_identity` — direct consequence:
  `|C1| + |C2| + |C3| = |A| + 3`.
* `CapTriple.exists_surplus_cap_of_card_gt_nine` — pigeonhole on the
  cap triple: if `|A| > 9` then some cap has size `> 4`.

## SurplusCapPacket: moved downstream

The MEC-aware `SurplusCapPacket` (carrying a non-obtuse circumscribed
Moser triangle together with the cap-triple over its structural
projection) is defined in `CapPartitionFromMEC.lean`. The packet
records the geometric promotion data that downstream U1 sub-lemmas
consume through `cap_arc_midpoint_inequality_v{1,2,3}`.

## What is *not* proven here

The genuine geometric content of U1 — that *every* minimal strict-convex
PerVertexK4 counterexample with a surplus cap admits a Moser triangle
in the `(m, 4, 4)` regime — is a sequence of five sub-lemmas which
require MEC / Apollonius geometry that this scaffold does not build.
See `U1TwoShortCapReduction.lean` for the U1 statement and the open
sub-lemmas it depends on.
-/

open scoped EuclideanGeometry
open Finset



/- ### Moser triangle: three labelled vertices of `A` -/





variable {A : Finset ℝ²}









/- ### `CapTriple`: closed-cap labelled triple on `A`

Closed-cap convention:

* `Ci` is the closed chain between `v_{i+1}` and `v_{i+2}` not passing
  through `v_i`, *including* its two Moser-vertex endpoints.
* Therefore `v_i ∉ Ci` (opposite apex never in its own opposite cap),
  while `v_{i+1}, v_{i+2} ∈ Ci`.
* Each Moser vertex is in exactly two caps.
* Each non-Moser vertex is in exactly one cap.
* `C1 ∪ C2 ∪ C3 = A`.

This is the exact membership pattern packaged by the combinatorial
`Problem97.CapPartition`; the geometric `CapTriple` just records the
specialization to a Moser-vertex set produced by a `MoserTriangle`. -/





variable {A : Finset ℝ²} {M : MoserTriangle A}





/-- **Cap-sum identity (closed-cap form).**  For any cap triple of `A`,
`|C1| + |C2| + |C3| = |A| + 3`.

Direct from `Problem97.CapPartition.cap_sum_identity` via
`toCapPartition`. -/
theorem Problem97.CapTriple.cap_sum_identity (CP : CapTriple A M) :
    CP.C1.card + CP.C2.card + CP.C3.card = A.card + 3 :=
  Problem97.cap_sum_identity (cp := CP.toCapPartition)







/-! Note: `SurplusCapPacket`, its derived selectors `surplusCap`,
`oppCap1`, `oppCap2`, the `capSum` lemma, the existence theorem
`CapTriple.toSurplusCapPacket_of_card_gt_nine`, and the `(m, 4, 4)`
regime predicate `IsM44` (with its consequences) have been moved
downstream into `Erdos9796Proof.P97.CapPartitionFromMEC`, where the
MEC promotion data (a `MEC.NonObtuseCircumscribedMoserTriangle` and
its circumscribed-case-split witness) can be carried directly inside
the packet. This is the prerequisite for downstream U1 sub-lemmas to
apply `cap_arc_midpoint_inequality_v{1,2,3}` without manual MEC
construction. -/

end Erdos9796CountingFragment_Erdos9796Proof_P97_Cap_Structure

section Erdos9796CountingFragment_Erdos9796Proof_P97_Moser_NonDeg

open Problem97 Problem97.MEC

/- Fragment from Erdos9796Proof.P97.Moser.NonDeg; source SHA-256 dd0335fd4a8de1d4d259bdc5a1fcac46e7a179fe1304481d159a516764ebdac7 -/


/-!
# Moser triangle vertices are noncollinear: nonzero signed area

The circumscribed branch of `Problem97.MEC.MoserTriangle` carries three
pairwise distinct `A`-vertices on the MEC boundary. This file proves that
those three vertices have nonzero `signedArea2`, which the downstream
cap-partition consumer (`Problem97.MEC.cap_partition_from_moser_circumscribed`)
needs to discharge its `hMoserNonDeg` hypothesis.

## Mathematical content

Three distinct points equidistant from a common center cannot be
collinear: a line meets a circle in at most two points. We package
this via Mathlib's strict-convex-space machinery:

* If three collinear points lie on a circle, one is `Wbtw` of the other
  two by `Collinear.wbtw_or_wbtw_or_wbtw`. With pairwise distinctness
  this strengthens to `Sbtw`, and `Sbtw.dist_lt_max_dist` gives a
  strictly smaller distance to the center — contradicting equidistance.

To translate to `signedArea2`, we prove
`signedArea2 v1 v2 v3 = 0 → Collinear ℝ {v1, v2, v3}` directly from the
2D cross-product identity (case analysis on which coordinate of
`v2 - v1` is nonzero, picking the scalar accordingly).

## Main declarations

* `Problem97.collinear_of_signedArea2_eq_zero` — algebraic predicate
  `signedArea2 = 0` implies the three points are collinear.
* `Problem97.MEC.not_collinear_of_three_dist_eq` — three distinct
  equidistant points are noncollinear (uses `StrictConvexSpace ℝ ℝ²`).
* `Problem97.MEC.signedArea2_ne_zero_of_three_dist_eq` — combining the
  two: three distinct equidistant points have nonzero signed area.
* `Problem97.MEC.moser_triangle_signed_area_ne_zero` — the target
  theorem applied to the circumscribed branch of `MoserTriangle`.
-/

open scoped EuclideanGeometry
open Finset











/-- **Three distinct equidistant points have nonzero signed area.** Combine
`Problem97.collinear_of_signedArea2_eq_zero` (contrapositive) with
`Problem97.MEC.not_collinear_of_three_dist_eq`. -/
lemma Problem97.MEC.signedArea2_ne_zero_of_three_dist_eq {p₁ p₂ p₃ c : ℝ²} {r : ℝ}
    (h1 : dist p₁ c = r) (h2 : dist p₂ c = r) (h3 : dist p₃ c = r)
    (h12 : p₁ ≠ p₂) (h23 : p₂ ≠ p₃) (h13 : p₁ ≠ p₃) :
    Problem97.signedArea2 p₁ p₂ p₃ ≠ 0 := by
  intro hz
  exact not_collinear_of_three_dist_eq h1 h2 h3 h12 h23 h13
    (Problem97.collinear_of_signedArea2_eq_zero p₁ p₂ p₃ hz)

/-- **Target theorem.** In the circumscribed branch of the Sylvester
dichotomy (`MoserTriangle.case_split = Or.inl _`), the three Moser
triangle vertices are pairwise distinct points on the MEC boundary
(`dist vᵢ (mec A hA).center = (mec A hA).radius`), hence noncollinear,
hence `signedArea2 ≠ 0`. This discharges the `hMoserNonDeg` hypothesis
of `Problem97.MEC.cap_partition_from_moser_circumscribed`. -/
theorem Problem97.MEC.moser_triangle_signed_area_ne_zero
    {A : Finset ℝ²} {hA : A.Nonempty} {hncol : ¬ Collinear ℝ (A : Set ℝ²)}
    (MT : Problem97.MEC.MoserTriangle A hA hncol)
    (hCircumscribed : ∃ h12 h23 h13,
      MT.case_split = Or.inl ⟨h12, h23, h13⟩) :
    Problem97.signedArea2 MT.v1 MT.v2 MT.v3 ≠ 0 := by
  obtain ⟨h12, h23, h13, _⟩ := hCircumscribed
  exact signedArea2_ne_zero_of_three_dist_eq
    MT.v1_boundary MT.v2_boundary MT.v3_boundary h12 h23 h13

end Erdos9796CountingFragment_Erdos9796Proof_P97_Moser_NonDeg

section Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_L4

open Problem97 Problem97.Dumitrescu

/- Fragment from Erdos9796Proof.P97.Dumitrescu.L4; source SHA-256 e83e9f54d8942578d2c5ed7d0655ace7578bc914fb411a46c1c9edcd9760b89a -/


/-!
# Dumitrescu L4: three-cap decomposition (Problem 97)

`Problem97.Dumitrescu.three_cap_decomposition` packages the heavy
MEC + Moser-triangle + cap-partition machinery into the headline
combinatorial statement used downstream by Dumitrescu L5–L8:

  *From a convex-independent finite point set `A ⊆ ℝ²` and a Moser
  triangle on `A` in the **circumscribed branch** of the Sylvester
  dichotomy, one obtains a closed cap triple `C1, C2, C3 ⊆ A`
  satisfying the cap-sum identity*

    `|C1| + |C2| + |C3| = |A| + 3`.

This is a pure composition lemma — every load-bearing geometric step
is discharged by an existing proven theorem:

* `Problem97.MEC.moser_triangle_signed_area_ne_zero` discharges the
  Moser-nondegeneracy hypothesis `hMoserNonDeg` (`MoserNonDeg.lean`).
* `Problem97.MEC.arc_partition_count_eq_one` discharges the
  cap-count hypothesis `hAGenericCapCount` (`ArcPartitionCount.lean`).
* `Problem97.MEC.cap_partition_from_moser_circumscribed` assembles
  the `CapTriple` from those two pieces (`CapPartitionFromMEC.lean`).
* `Problem97.CapTriple.cap_sum_identity` gives the cap-sum identity
  (`CapStructure.lean`).

## Branch convention

L4 is stated **restricted to the circumscribed branch**: the
`hCircumscribed` hypothesis selects the left disjunct of the Sylvester
dichotomy (three pairwise distinct MEC-boundary vertices), matching the
existing `cap_partition_from_moser_circumscribed` shape. The diameter
branch (`Or.inr _`) is closed by a separate K4-driven exclusion lemma
(`p97-mec-no-diameter-under-k4`); consumers that need to handle a raw
Moser triangle case-split on `MT.case_split` themselves before invoking
`three_cap_decomposition`. Keeping L4 as a pure composition lemma keeps
the dependency chain L4 → {arc count, Moser non-degeneracy, cap-from-MEC,
cap-sum} clean and free of the K4 antecedent.

## References

* Adrian Dumitrescu (2006), *On Distinct Distances from a Vertex of a Convex Polygon*, Discrete & Computational Geometry 36, 503–509. DOI: 10.1007/s00454-006-1262-y.
* Gabriel Nivasch, János Pach, Rom Pinchasi, and Shira Zerbib, *The Number of Distinct Distances from a Vertex of a Convex Polygon*, Journal of Computational Geometry 4 (2013), 1–12; arXiv:1207.1266 (2012 preprint).
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical





theorem solution
    {A : Finset ℝ²} {hA : A.Nonempty} {hncol : ¬ Collinear ℝ (A : Set ℝ²)}
    (hConv : Problem97.ConvexIndep A)
    (MT : Problem97.MEC.MoserTriangle A hA hncol)
    (hCircumscribed : ∃ h12 h23 h13,
      MT.case_split = Or.inl ⟨h12, h23, h13⟩) :
    ∃ CP : Problem97.CapTriple A (MT.toStructural hCircumscribed),
      CP.C1.card + CP.C2.card + CP.C3.card = A.card + 3 := by
  -- 1. Discharge `hMoserNonDeg`: three distinct equidistant MEC-boundary
  --    vertices have nonzero signed area (MoserNonDeg.lean).
  have hMoserNonDeg :
      Problem97.signedArea2 MT.v1 MT.v2 MT.v3 ≠ 0 :=
    Problem97.MEC.moser_triangle_signed_area_ne_zero MT hCircumscribed
  -- 2. Discharge `hAGenericCapCount`: every non-Moser `A`-vertex lies on
  --    exactly one of the three closed caps (ArcPartitionCount.lean).
  have hAGenericCapCount :
      ∀ v ∈ A, v ≠ MT.v1 → v ≠ MT.v2 → v ≠ MT.v3 →
        (if Problem97.OnArcOpposite MT.v1 MT.v2 MT.v3 v then 1 else 0)
          + (if Problem97.OnArcOpposite MT.v2 MT.v3 MT.v1 v then 1 else 0)
          + (if Problem97.OnArcOpposite MT.v3 MT.v1 MT.v2 v then 1 else 0)
          = 1 :=
    Problem97.MEC.arc_partition_count_eq_one hConv MT hCircumscribed
  -- 3. Build the cap triple (CapPartitionFromMEC.lean).
  obtain ⟨CP⟩ :=
    Problem97.MEC.cap_partition_from_moser_circumscribed
      MT hCircumscribed hMoserNonDeg hAGenericCapCount
  -- 4. The cap-sum identity is the existing CapTriple lemma
  --    (CapStructure.lean).
  exact ⟨CP, CP.cap_sum_identity⟩

end Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_L4
