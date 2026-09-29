-- Prove2me | solution 1 for Problem97.Dumitrescu.capPairApexes_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:48.893432+00:00
-- url     : https://prove2.me/submissions/d75a6fa3-21ab-4c1f-a366-08d9ecfd373d

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.Dumitrescu.L6:4994:6521. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Dumitrescu_L6
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Theorems.Thm_Problem97_Dumitrescu_perpBisector_apex_bound

section Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_L3

open Problem97 Problem97.Dumitrescu

/- Fragment from Erdos9796Proof.P97.Dumitrescu.L3; source SHA-256 26c1b07fe4e05707f22f498cfd8a3606d92084c27d0a2f7cb7580cf88c86e5fa -/


/-!
# Dumitrescu L3: trivial edge-isosceles bound (Problem 97)

`Problem97.Dumitrescu.trivial_edge_bound` is Dumitrescu's Lemma 3
(Dumitrescu 2006 / Nivasch–Pach–Pinchasi–Zerbib 2013, arXiv:1207.1266 §2):

  For any finite point set `A ⊆ ℝ²` and any base pair `(b, c)` with
  `b, c ∈ A` and `b ≠ c`, the number of apexes `a ∈ A` with `a ∉ {b, c}`
  forming an isosceles triangle with base `bc` (i.e. `dist a b = dist a c`)
  is bounded above by the total number of points in `A` on the
  perpendicular bisector of `bc`.

This is one of the smallest lemmas in the Dumitrescu L1–L10 chain: it
simply says that filtering with a strictly stronger predicate
(`a ∉ {b, c} ∧ dist a b = dist a c`) yields a subset of filtering with
the weaker predicate (`dist a b = dist a c`). Its purpose is to provide
a clean named hook for the per-base apex count used in L6
(`p97-dumitrescu-l6-cap-good-edge-quadratic`).

Combined with L1 (`Problem97.Dumitrescu.perpBisector_apex_bound`), the
right-hand side is bounded by `2` under `ConvexIndep A`, giving the
useful corollary `trivial_edge_bound_of_convexIndep`: each base edge of
a convex-independent point set contributes at most `2` non-base apexes
forming isosceles triangles with it.

## Proof strategy

The main inequality is `Finset.card_le_card` applied to
`Finset.monotone_filter_right`, since the predicate
`a ∉ {b, c} ∧ dist a b = dist a c` clearly implies `dist a b = dist a c`.
The convex-independent corollary chains this with L1.

## References

* Adrian Dumitrescu (2006), *On Distinct Distances from a Vertex of a Convex Polygon*, Discrete & Computational Geometry 36, 503–509. DOI: 10.1007/s00454-006-1262-y.
* Gabriel Nivasch, János Pach, Rom Pinchasi, and Shira Zerbib, *The Number of Distinct Distances from a Vertex of a Convex Polygon*, Journal of Computational Geometry 4 (2013), 1–12; arXiv:1207.1266 (2012 preprint).
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical




/-- **Dumitrescu L3 / trivial edge-isosceles bound.**

For any finite point set `A ⊆ ℝ²` and any base pair `(b, c)` with
`b, c ∈ A` and `b ≠ c`, the number of non-base apexes `a ∈ A \ {b, c}`
forming an isosceles triangle with base `bc` is at most the total
number of points of `A` on the perpendicular bisector of `bc`. The
proof is the trivial subset inclusion: filtering by the stronger
predicate gives a subset of filtering by the weaker one. -/
theorem Problem97.Dumitrescu.trivial_edge_bound
    {A : Finset ℝ²} {b c : ℝ²} (_hb : b ∈ A) (_hc : c ∈ A) (_hbc : b ≠ c) :
    (A.filter (fun a => a ∉ ({b, c} : Finset ℝ²) ∧ dist a b = dist a c)).card ≤
      (A.filter (fun a => dist a b = dist a c)).card := by
  refine Finset.card_le_card ?_
  exact Finset.monotone_filter_right A (fun _a _ha hand => hand.2)

/-- **Dumitrescu L3, convex-independent corollary.**

For a convex-independent finite point set `A ⊆ ℝ²` and any base pair
`(b, c)` with `b, c ∈ A` and `b ≠ c`, at most `2` non-base apexes
`a ∈ A \ {b, c}` form an isosceles triangle with base `bc`. Chains
`trivial_edge_bound` with `perpBisector_apex_bound` (L1). -/
theorem Problem97.Dumitrescu.trivial_edge_bound_of_convexIndep
    {A : Finset ℝ²} (hA : ConvexIndep A)
    {b c : ℝ²} (hb : b ∈ A) (hc : c ∈ A) (hbc : b ≠ c) :
    (A.filter (fun a => a ∉ ({b, c} : Finset ℝ²) ∧ dist a b = dist a c)).card ≤ 2 :=
  (trivial_edge_bound hb hc hbc).trans (perpBisector_apex_bound hA hb hc hbc)

end Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_L3

section Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_L6

open Problem97 Problem97.Dumitrescu

/- Fragment from Erdos9796Proof.P97.Dumitrescu.L6; source SHA-256 5734bd5bf1734a3ac1aec799aa89c43c6d0b026d07909ee8e7389ee71d40d90e -/


/-!
# Dumitrescu L6: cap good-edge quadratic bound (Corollary 9)

`Problem97.Dumitrescu.cap_good_edge_quadratic_of_ranking` and
`Problem97.Dumitrescu.cap_good_edge_quadratic` are the two forms of
Dumitrescu's Lemma 6 / Corollary 9
(Dumitrescu 2006 / Nivasch–Pach–Pinchasi–Zerbib 2013 (2012 preprint),
arXiv:1207.1266 §2 Corollary 9):

  Within a single convex-independent cap `C ⊆ A` of size `m`, the
  total **(witness-pair, non-base apex)** incidence count is `O(m²)`,
  where each cap witness pair `xy ∈ capWitnessPairs A C` contributes at
  most `2` non-base apexes (via L3) and the witness pair count itself
  is bounded by `m - 1` under a `CapWitnessRanking` (via L5) or
  unconditionally by `Nat.choose m 2` (via the trivial subset bound).

This file corresponds to the blueprint obligation
`p97-dumitrescu-l6-cap-good-edge-quadratic`.

## Composition

The proof is a clean double-count:

* **Per-pair apex bound (L3).**  For each base pair `(x, y)` with
  `x, y ∈ A`, `x ≠ y`,
  `Problem97.Dumitrescu.trivial_edge_bound_of_convexIndep` gives
  `|{a ∈ A : a ∉ {x, y} ∧ dist a x = dist a y}| ≤ 2`
  under `ConvexIndep A`.

* **Witness-pair count (L5 / unconditional).**  L5
  (`Problem97.Dumitrescu.cap_witness_uniqueness`) gives
  `|capWitnessPairs A C| ≤ C.card - 1` from a `CapWitnessRanking A C`;
  the unconditional fallback
  (`Problem97.Dumitrescu.capWitnessPairs_card_le_choose_two`) gives
  `|capWitnessPairs A C| ≤ Nat.choose C.card 2`.

* **Sum.**  Sum the per-pair bound `2` over the witness pairs.
  Multiplying gives the headline quadratic bound `O(m²)`.

The result is consumed by
`p97-dumitrescu-l8-three-cap-good-edge-count` (Corollary 10), which
sums over the three caps of a `CapTriple` and adds the
`crossCapEdges` count from L7.

## Per-pair apex Finset

The per-pair object is

```
capPairApexes A xy := A.filter (fun a => a ∉ xy ∧ ∃ r, ∀ q ∈ xy, dist a q = r)
```

which is the *unfolded* form of the L2 reindexing of
`Problem97.IsoscelesPairsAt` at base `xy`. By construction it ignores
the cap membership of the apex: a "good apex" for the chord `xy` can
sit anywhere in `A` (inside or outside `C`) as long as it is not on
the chord itself. This matches the paper's good-edge definition and
gives a strictly larger count than the cap-witness-pair count (which
requires apex `∉ C`); the L3 bound `≤ 2` applies in both settings.

## What this file does *not* assume

No `axiom` declarations. No vacuous `:= True` predicates. The two
headline theorems take a `ConvexIndep A` hypothesis (consumed by L3)
plus either a `CapWitnessRanking A C` (linear bound) or no extra
hypothesis (quadratic bound). All the heavy lifting (geometric
content of L1, witness-pair structure, ranking machinery) lives in
sibling files `DumitrescuL1.lean`, `DumitrescuL3.lean`,
`DumitrescuL5.lean`. L6 is the arithmetic composition.

## References

* Adrian Dumitrescu (2006), *On Distinct Distances from a Vertex of a Convex Polygon*, Discrete & Computational Geometry 36, 503–509. DOI: 10.1007/s00454-006-1262-y. (Original Lemma 6.)
* Gabriel Nivasch, János Pach, Rom Pinchasi, and Shira Zerbib, *The Number of Distinct Distances from a Vertex of a Convex Polygon*, Journal of Computational Geometry 4 (2013), 1–12; arXiv:1207.1266 (2012 preprint), Corollary 9.
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical




/- ### Per-pair apex filter

For a `2`-element subset `xy ⊆ A`, the *per-pair apex set* is the
collection of points `a ∈ A` with `a ∉ xy` and all points of `xy`
equidistant from `a`. Equivalently, `a` lies on the perpendicular
bisector of the chord `xy` and is not an endpoint. This is the L2
reindexing form (`Problem97.IsoscelesPairsAt` recast as a filter at a
fixed base) used for the per-pair contribution to the cap good-edge
count.

We keep the apex filter `A`-wide (not restricted to `A \ C`): the L3
bound `≤ 2` applies regardless, and the larger count subsumes both
the in-cap and out-of-cap apex contributions used downstream. -/




theorem solution
    {A : Finset ℝ²} (hA : ConvexIndep A)
    {xy : Finset ℝ²} (hxy_sub : xy ⊆ A) (hxy_card : xy.card = 2) :
    (capPairApexes A xy).card ≤ 2 := by
  -- Extract the two endpoints `b ≠ c` of `xy`.
  rw [Finset.card_eq_two] at hxy_card
  obtain ⟨b, c, hbc, hxy_eq⟩ := hxy_card
  subst hxy_eq
  have hbA : b ∈ A := hxy_sub (by simp)
  have hcA : c ∈ A := hxy_sub (by simp)
  -- `capPairApexes A {b, c}` is contained in the L3 filter at base `(b, c)`.
  have hsubfil :
      capPairApexes A ({b, c} : Finset ℝ²) ⊆
        A.filter (fun a => a ∉ ({b, c} : Finset ℝ²) ∧ dist a b = dist a c) := by
    intro a ha
    unfold capPairApexes at ha
    rw [Finset.mem_filter] at ha ⊢
    obtain ⟨haA, hans, r, hr⟩ := ha
    refine ⟨haA, hans, ?_⟩
    rw [hr b (by simp), hr c (by simp)]
  calc (capPairApexes A ({b, c} : Finset ℝ²)).card
      ≤ (A.filter (fun a => a ∉ ({b, c} : Finset ℝ²) ∧ dist a b = dist a c)).card :=
        Finset.card_le_card hsubfil
    _ ≤ 2 := trivial_edge_bound_of_convexIndep hA hbA hcA hbc



/- ### The (witness-pair, apex) double count

For a cap `C ⊆ A`, we sum `(capPairApexes A xy).card` over
`xy ∈ capWitnessPairs A C`. By the per-pair bound this is at most
`2 * |capWitnessPairs A C|`. Bounding the witness-pair count itself
(by L5 with a ranking, or by the unconditional `Nat.choose m 2`)
yields the headline quadratic bound. -/

end Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_L6
