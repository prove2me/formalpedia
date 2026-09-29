-- Prove2me | solution 1 for Problem97.CGN8_circumscribed_iCount_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:07:27.694313+00:00
-- url     : https://prove2.me/submissions/525047e8-3699-490e-b011-38496ff94445

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN8:854:33243. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN4g
import Definitions.Def_Erdos9796Counting_CGN_CGN6
import Definitions.Def_Erdos9796Counting_Cap_PartitionFromMEC
import Definitions.Def_Erdos9796Counting_Cap_Structure
import Definitions.Def_Erdos9796Counting_CircumscribedMECPacket
import Definitions.Def_Erdos9796Counting_Dumitrescu_L6
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Definitions.Def_Erdos9796Counting_Moser_Triangle
import Definitions.Def_Erdos9796Counting_Moser_TriangleNonObtuse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Linarith
import Theorems.Thm_Problem97_CGN_CGN4g_strictCapBlockData_of_supportCap_oriented
import Theorems.Thm_Problem97_CGN_CGN6c_oneSidedDistanceInjective
import Theorems.Thm_Problem97_CGN_CGN6e2_not_two_apices_on_complementary_side
import Theorems.Thm_Problem97_CGN_CGN6norm_minorCapChainModel_of_mecCapPacket
import Theorems.Thm_Problem97_CGN_capPairApexes_mem_edgeAt_packet
import Theorems.Thm_Problem97_CGN_edgeAt_injective_on_CapIndexPairs
import Theorems.Thm_Problem97_CGN_edgeAt_mem_powersetCard
import Theorems.Thm_Problem97_CGN_witnessedPairsAt_sum_le_square_div_four
import Theorems.Thm_Problem97_ConvexIndep_not_wbtw
import Theorems.Thm_Problem97_Dumitrescu_capPairApexes_card_le_two
import Theorems.Thm_Problem97_Dumitrescu_three_cap_decomposition
import Theorems.Thm_Problem97_MEC_exists_nonobtuse_circumscribed_triple
import Theorems.Thm_Problem97_signedArea2_eq_zero_iff_collinear

section Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN

open Problem97 Problem97.CGN Problem97.CGN.OrderedCap

/- Fragment from Erdos9796Proof.P97.CGN.CGN; source SHA-256 9f1ccd7df30637d7fbdf412fb40177dedb5193c45ec2993df86f137cbd34ffb7 -/


/-!
# CGN7: indexed cap-side witness matching scaffold

This file records the CGN7-local indexed witness relation requested by the
updated counterexample-card-ge-nine prose.  The geometry that produces the
one-sided injectivity hypotheses lives in the CGN6 lemmas; this module only
packages the ordered-cap interface and the partial-matching counting shell.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace
open Finset








variable {m : ℕ}



@[simp] theorem Problem97.CGN.OrderedCap.map_points (L : OrderedCap m) (T : ℝ² → ℝ²)
    (hT : Function.Injective T) (i : Fin m) :
    (L.map T hT).points i = T (L.points i) := rfl

























/-- Membership in `WitnessedPairsAt` is exactly the indexed witness relation. -/
@[simp] theorem Problem97.CGN.mem_WitnessedPairsAt_iff {m : ℕ} {L : OrderedCap m} {j : Fin m}
    {p : Fin m × Fin m} :
    p ∈ WitnessedPairsAt L j ↔ WitnessesCapEdgeAt L j p.1 p.2 := by
  classical
  unfold WitnessedPairsAt
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩











/-- An index pair belongs to `CapIndexPairs m` exactly when it is oriented
strictly increasingly. -/
@[simp] theorem Problem97.CGN.mem_CapIndexPairs {m : ℕ} {p : Fin m × Fin m} :
    p ∈ CapIndexPairs m ↔ p.1 < p.2 := by
  simp [CapIndexPairs]











/-- From `2 ≤ card`, extract two distinct members of the finite apex set. -/
theorem Problem97.CGN.two_mem_capPairApexes_of_two_le_card {m : ℕ} {L : OrderedCap m}
    {A : Finset ℝ²} {r s : Fin m}
    (h2 : 2 ≤ (Problem97.Dumitrescu.capPairApexes A (edgeAt L r s)).card) :
    ∃ a b,
      a ≠ b ∧
      a ∈ Problem97.Dumitrescu.capPairApexes A (edgeAt L r s) ∧
      b ∈ Problem97.Dumitrescu.capPairApexes A (edgeAt L r s) := by
  have h1 : 1 < (Problem97.Dumitrescu.capPairApexes A (edgeAt L r s)).card := by
    omega
  rcases Finset.one_lt_card.mp h1 with ⟨a, ha, b, hb, hab⟩
  exact ⟨a, b, hab, ha, hb⟩



-- The next two CGN7c theorems depend on the missing CGN6e indexed-witness
-- bridge.  Stop here rather than inventing that geometry.

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN

section Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN4g

open Problem97 Problem97.CGN Problem97.CGN.StrictCapBlockData

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












variable {A C : Finset ℝ²}

/-- The retained local cap image is exactly the support cap. -/
theorem Problem97.CGN.StrictCapBlockData.cap_image (B : StrictCapBlockData A C) :
    Finset.univ.image B.L.points = C :=
  B.Block.cap_image



























































/-- CGN8 step-2 packaging wrapper: turn one support-cap description into the
ordered-cap packet consumed by CGN6 / CGN7.  This theorem is packaging only:
the proof routes through the retained-block version and forgets the global
boundary interval block. -/
theorem Problem97.CGN.CGN4g_capData_of_supportCap_oriented
    {A C : Finset ℝ²} {M : Problem97.MoserTriangle A}
    (hA : Problem97.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²))
    (hC_subset : C ⊆ A)
    (hC_arc : ∀ x ∈ A, x ∈ C ↔ Problem97.OnArcOpposite M.v1 M.v2 M.v3 x)
    (hv_mem : M.v2 ∈ C)
    (hw_mem : M.v3 ∈ C)
    (P : Problem97.CircumscribedMECPacket A M)
    (hacute : 0 ≤ ⟪M.v2 - M.v1, M.v3 - M.v1⟫_ℝ) :
    ∃ m, ∃ L : OrderedCap m,
      ∃ Packet : MecCapPacket A L,
      ∃ Hside : MinorCapSideHypotheses Packet,
      ∃ Hord : StrictCapOrder A L,
        Finset.univ.image L.points = C ∧
          ((L.points (firstIndex Packet.hm) = M.v2 ∧
              L.points (lastIndex Packet.hm) = M.v3) ∨
            (L.points (firstIndex Packet.hm) = M.v3 ∧
              L.points (lastIndex Packet.hm) = M.v2)) := by
  rcases CGN4g_strictCapBlockData_of_supportCap_oriented
      (A := A) (C := C) (M := M) hA hnoncoll hC_subset hC_arc hv_mem hw_mem
      P hacute with
    ⟨B, horient⟩
  exact ⟨B.m, B.L, B.Packet, B.Hside, B.Hord, B.cap_image, horient⟩



/-- Drop the endpoint-orientation packet when only the bare cap data is
needed. -/
theorem Problem97.CGN.CGN4g_capData_of_supportCap
    {A C : Finset ℝ²} {M : Problem97.MoserTriangle A}
    (hA : Problem97.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²))
    (hC_subset : C ⊆ A)
    (hC_arc : ∀ x ∈ A, x ∈ C ↔ Problem97.OnArcOpposite M.v1 M.v2 M.v3 x)
    (hv_mem : M.v2 ∈ C)
    (hw_mem : M.v3 ∈ C)
    (P : Problem97.CircumscribedMECPacket A M)
    (hacute : 0 ≤ ⟪M.v2 - M.v1, M.v3 - M.v1⟫_ℝ) :
    ∃ m, ∃ L : OrderedCap m,
      ∃ Packet : MecCapPacket A L,
      ∃ Hside : MinorCapSideHypotheses Packet,
      ∃ Hord : StrictCapOrder A L,
        Finset.univ.image L.points = C := by
  rcases CGN4g_capData_of_supportCap_oriented
      (A := A) (C := C) (M := M) hA hnoncoll hC_subset hC_arc hv_mem hw_mem P hacute with
    ⟨m, L, Packet, Hside, Hord, hLC, _⟩
  exact ⟨m, L, Packet, Hside, Hord, hLC⟩

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN4g

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

section Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_L10

open Problem97 Problem97.Dumitrescu

/- Fragment from Erdos9796Proof.P97.Dumitrescu.L10; source SHA-256 02026039f0b36ebf12c5fd42a39cfae659da0a191c1eae2ebecb572320b3f76f -/


/-!
# Dumitrescu L10a: base-pair reindex identity

`Problem97.Dumitrescu.iCount_eq_sum_capPairApexes` is the pure-combinatorial
identity (Dumitrescu lane L10a):

  `iCount A = ∑_{xy ∈ A.powersetCard 2} (capPairApexes A xy).card`

This is obtained by the same base/apex summation-swap used in the L2 proof:
reindex `IsoscelesPairsAt A a` as a filter on `A.powersetCard 2`, swap the
two sums via `Finset.sum_comm`, then recognize the inner filter as
`capPairApexes`.

No geometric content is required; all steps are pure Finset arithmetic.

Blueprint obligation: `p97-dumitrescu-l10a-base-pair-reindex`.
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical




/-- Reindex `IsoscelesPairsAt A p` as a filter on `A.powersetCard 2`:
a 2-element subset `s ⊆ A` is an isosceles-pair at apex `p` iff
`p ∉ s` and all points of `s` are equidistant from `p`.

(This is the same rewriting used internally in the L2 proof; we
re-state it here to keep L10a self-contained.) -/
 lemma Problem97.Dumitrescu.isoscelesPairsAt_eq_filter_powersetCard_l10
    (A : Finset ℝ²) (p : ℝ²) :
    Problem97.IsoscelesPairsAt A p =
      (A.powersetCard 2).filter
        (fun s => p ∉ s ∧ ∃ r : ℝ, ∀ q ∈ s, dist p q = r) := by
  ext s
  unfold Problem97.IsoscelesPairsAt
  rw [Finset.mem_filter, Finset.mem_filter,
      Finset.mem_powersetCard, Finset.mem_powersetCard]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨hsub, hcard⟩, hex⟩
    refine ⟨⟨?_, hcard⟩, ?_, hex⟩
    · exact hsub.trans (Finset.erase_subset _ _)
    · intro hp
      have := hsub hp
      rw [Finset.mem_erase] at this
      exact this.1 rfl
  · rintro ⟨⟨hsub, hcard⟩, hpns, hex⟩
    refine ⟨⟨?_, hcard⟩, hex⟩
    intro q hq
    rw [Finset.mem_erase]
    refine ⟨?_, hsub hq⟩
    intro h; subst h; exact hpns hq

/-- **L10a — base-pair reindex identity.**

The total isosceles count of `A` equals the sum over all unordered base
pairs `xy ∈ A.powersetCard 2` of the number of apexes `(capPairApexes A xy).card`:

  `iCount A = ∑_{xy ∈ A.powersetCard 2} (capPairApexes A xy).card`.

Pure combinatorics (no geometric content).  The proof is a direct
summation swap: reindex the inner `IsoscelesPairsAt A a` as a filter
on `A.powersetCard 2`, apply `Finset.sum_comm` to swap apex/base sums,
then recognise the inner accumulation as `capPairApexes`. -/
theorem Problem97.Dumitrescu.iCount_eq_sum_capPairApexes (A : Finset ℝ²) :
    iCount A = ∑ xy ∈ A.powersetCard 2, (capPairApexes A xy).card := by
  unfold iCount iCountAt
  -- Step 1: reindex each IsoscelesPairsAt as a filter on A.powersetCard 2.
  simp_rw [Problem97.Dumitrescu.isoscelesPairsAt_eq_filter_powersetCard_l10 A]
  -- Step 2: convert card to sum of indicators, swap sums, convert back.
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.card_filter]
  -- Step 3: recognise the inner filter as capPairApexes.
  simp only [capPairApexes]

/-!
## L10b — base-pair cap partition

Every 2-element subset of `A` lies in exactly one of the four families:
the three intra-cap `Cᵢ.powersetCard 2` collections and `crossCapEdges CP`.

### Why the four families are pairwise disjoint

- **Intra-cap vs intra-cap:** Any two distinct caps `Cᵢ, Cⱼ` share at
  most one point (the third Moser vertex, by closed-cap convention).
  So no 2-element subset can be a subset of both.
- **Intra-cap vs cross-cap:** `crossCapEdges CP` consists of 2-subsets
  NOT contained in any single cap, so every intra-cap pair is excluded.

### Why the four families cover `A.powersetCard 2`

Given any `uv ∈ A.powersetCard 2`, either `uv ⊆ C1` or `uv ⊆ C2` or
`uv ⊆ C3`, or none of these holds — in the last case `uv ∈ crossCapEdges`.

Blueprint obligation: `p97-dumitrescu-l10b-base-pair-cap-partition`.
-/

/-- **Disjointness: `C1.powersetCard 2` vs `C2.powersetCard 2`.**

Any 2-element subset of `C1 ∩ C2` would have both elements in
both caps.  But `C1 ∩ C2 ⊆ {M.v3}` (cardinality ≤ 1) by the
closed-cap convention, so no such subset exists. -/
 lemma Problem97.Dumitrescu.disjoint_powersetCard2_C1_C2
    {A : Finset ℝ²} {M : Problem97.MoserTriangle A}
    (CP : Problem97.CapTriple A M) :
    Disjoint (CP.C1.powersetCard 2) (CP.C2.powersetCard 2) := by
  classical
  rw [Finset.disjoint_left]
  intro xy hxy1 hxy2
  rw [Finset.mem_powersetCard] at hxy1 hxy2
  obtain ⟨hxy1_sub, hxy1_card⟩ := hxy1
  obtain ⟨hxy2_sub, _⟩ := hxy2
  -- Every element of xy is in both C1 and C2, hence in C1 ∩ C2 ⊆ {v3}.
  have h_inter_subset : ∀ x ∈ xy, x = M.v3 := by
    intro x hx
    have hxC1 := hxy1_sub hx
    have hxC2 := hxy2_sub hx
    by_cases hxM : x ∈ M.verts
    · unfold Problem97.MoserTriangle.verts at hxM
      rcases Finset.mem_insert.mp hxM with rfl | hxM'
      · exact absurd hxC1 CP.v1_notin_C1
      · rcases Finset.mem_insert.mp hxM' with rfl | hxM''
        · exact absurd hxC2 CP.v2_notin_C2
        · exact Finset.mem_singleton.mp hxM''
    · have hxA := CP.C1_subset hxC1
      have hsum := CP.nonmoser_in_one x hxA hxM
      rw [if_pos hxC1, if_pos hxC2] at hsum
      omega
  have hxy_card_le : xy.card ≤ 1 := by
    calc xy.card
        ≤ ({M.v3} : Finset ℝ²).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_singleton]
          exact h_inter_subset x hx
      _ = 1 := Finset.card_singleton _
  omega

/-- **Disjointness: `C1.powersetCard 2` vs `C3.powersetCard 2`.**

`C1 ∩ C3 ⊆ {M.v2}` because `v1 ∉ C1` and `v3 ∉ C3`. -/
 lemma Problem97.Dumitrescu.disjoint_powersetCard2_C1_C3
    {A : Finset ℝ²} {M : Problem97.MoserTriangle A}
    (CP : Problem97.CapTriple A M) :
    Disjoint (CP.C1.powersetCard 2) (CP.C3.powersetCard 2) := by
  classical
  rw [Finset.disjoint_left]
  intro xy hxy1 hxy3
  rw [Finset.mem_powersetCard] at hxy1 hxy3
  obtain ⟨hxy1_sub, hxy1_card⟩ := hxy1
  obtain ⟨hxy3_sub, _⟩ := hxy3
  have h_inter_subset : ∀ x ∈ xy, x = M.v2 := by
    intro x hx
    have hxC1 := hxy1_sub hx
    have hxC3 := hxy3_sub hx
    by_cases hxM : x ∈ M.verts
    · unfold Problem97.MoserTriangle.verts at hxM
      rcases Finset.mem_insert.mp hxM with rfl | hxM'
      · exact absurd hxC1 CP.v1_notin_C1
      · rcases Finset.mem_insert.mp hxM' with rfl | hxM''
        · rfl
        · rcases Finset.mem_singleton.mp hxM'' with rfl
          exact absurd hxC3 CP.v3_notin_C3
    · have hxA := CP.C1_subset hxC1
      have hsum := CP.nonmoser_in_one x hxA hxM
      rw [if_pos hxC1, if_pos hxC3] at hsum
      omega
  have hxy_card_le : xy.card ≤ 1 := by
    calc xy.card
        ≤ ({M.v2} : Finset ℝ²).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_singleton]
          exact h_inter_subset x hx
      _ = 1 := Finset.card_singleton _
  omega

/-- **Disjointness: `C2.powersetCard 2` vs `C3.powersetCard 2`.**

`C2 ∩ C3 ⊆ {M.v1}` because `v2 ∉ C2` and `v3 ∉ C3`. -/
 lemma Problem97.Dumitrescu.disjoint_powersetCard2_C2_C3
    {A : Finset ℝ²} {M : Problem97.MoserTriangle A}
    (CP : Problem97.CapTriple A M) :
    Disjoint (CP.C2.powersetCard 2) (CP.C3.powersetCard 2) := by
  classical
  rw [Finset.disjoint_left]
  intro xy hxy2 hxy3
  rw [Finset.mem_powersetCard] at hxy2 hxy3
  obtain ⟨hxy2_sub, hxy2_card⟩ := hxy2
  obtain ⟨hxy3_sub, _⟩ := hxy3
  have h_inter_subset : ∀ x ∈ xy, x = M.v1 := by
    intro x hx
    have hxC2 := hxy2_sub hx
    have hxC3 := hxy3_sub hx
    by_cases hxM : x ∈ M.verts
    · unfold Problem97.MoserTriangle.verts at hxM
      rcases Finset.mem_insert.mp hxM with rfl | hxM'
      · rfl
      · rcases Finset.mem_insert.mp hxM' with rfl | hxM''
        · exact absurd hxC2 CP.v2_notin_C2
        · rcases Finset.mem_singleton.mp hxM'' with rfl
          exact absurd hxC3 CP.v3_notin_C3
    · have hxA := CP.C2_subset hxC2
      have hsum := CP.nonmoser_in_one x hxA hxM
      rw [if_pos hxC2, if_pos hxC3] at hsum
      omega
  have hxy_card_le : xy.card ≤ 1 := by
    calc xy.card
        ≤ ({M.v1} : Finset ℝ²).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_singleton]
          exact h_inter_subset x hx
      _ = 1 := Finset.card_singleton _
  omega







/-- **CGN8a: intra-cap base-pair families are disjoint.**

For a `CapTriple`, the three closed caps contribute pairwise disjoint
families of 2-element subsets: no two-element subset of `A` can lie in
two distinct closed caps. -/
theorem Problem97.Dumitrescu.cgn8a_intraCapBasePairs_disjoint
    {A : Finset ℝ²} {M : Problem97.MoserTriangle A}
    (CP : Problem97.CapTriple A M) :
    Disjoint (CP.C1.powersetCard 2) (CP.C2.powersetCard 2) ∧
      Disjoint (CP.C1.powersetCard 2) (CP.C3.powersetCard 2) ∧
      Disjoint (CP.C2.powersetCard 2) (CP.C3.powersetCard 2) := by
  exact ⟨Problem97.Dumitrescu.disjoint_powersetCard2_C1_C2 CP,
          ⟨Problem97.Dumitrescu.disjoint_powersetCard2_C1_C3 CP,
           Problem97.Dumitrescu.disjoint_powersetCard2_C2_C3 CP⟩⟩

end Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_L10

section Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_L9

open Problem97 Problem97.Dumitrescu

/- Fragment from Erdos9796Proof.P97.Dumitrescu.L9; source SHA-256 778a25db99de269bade0811a06f0e0c94fef00a8934b475bd97d07407461d4bf -/


/-!
# Dumitrescu L9: three-cap power-mean inequality

`Problem97.Dumitrescu.power_mean_three_caps` (real form) and
`Problem97.Dumitrescu.power_mean_three_caps_nat` (natural form) discharge
the abstract power-mean / Cauchy–Schwarz inequality used in the final
arithmetic assembly of Dumitrescu's isosceles upper bound
(Dumitrescu 2006 / Nivasch–Pach–Pinchasi–Zerbib 2013, arXiv:1207.1266 §2 final step).

The inequality has no geometric content: for any three nonnegative reals
`m₁, m₂, m₃` with `m₁ + m₂ + m₃ = N`,
  `N² / 3 ≤ m₁² + m₂² + m₃²`,
or equivalently in natural-number form (no division),
  `N² ≤ 3 · (m₁² + m₂² + m₃²)`.

In the Dumitrescu specialization `N = n + 3` and `m_i = |Cᵢ|` are the
sizes of the three caps, but the present file is purely about the
algebraic inequality. The downstream consumer is
`p97-dumitrescu-l10-final-bound`; see obligation
`p97-dumitrescu-l9-power-mean-three-caps` in `data/blueprint.db`.

## Proof strategy

Both forms are immediate from `(m_i - m_j)² ≥ 0` summed over the three
pairs: this expands to
  `2 (m₁² + m₂² + m₃²) ≥ 2 (m₁ m₂ + m₂ m₃ + m₁ m₃)`,
and combined with the expansion of `N² = (m₁ + m₂ + m₃)²` gives
  `N² ≤ 3 (m₁² + m₂² + m₃²)`.
`nlinarith` closes both goals from the three `sq_nonneg` hints once `N`
has been substituted with the sum.

Note: the nonnegativity hypotheses `h₁, h₂, h₃` in the real form are
not used by the proof — the inequality is Cauchy–Schwarz and holds for
all reals — but they are kept in the signature to match the convention
of downstream `Problem97.Dumitrescu.*` lemmas where cap sizes are
nonnegative by construction.
-/




/-- **Dumitrescu L9 (real form).**  Power-mean / Cauchy–Schwarz on three
nonnegative reals with a fixed sum: for `m₁ + m₂ + m₃ = N`,
`N² / 3 ≤ m₁² + m₂² + m₃²`, with equality iff `m₁ = m₂ = m₃ = N/3`.

Used in the final arithmetic assembly of the isosceles upper bound
(Dumitrescu 2006 eq. (5)) to extract the `(n+3)² / 12` term from the
three-cap good-edge count. -/
theorem Problem97.Dumitrescu.power_mean_three_caps
    {m₁ m₂ m₃ : ℝ} (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (h₃ : 0 ≤ m₃)
    {N : ℝ} (hsum : m₁ + m₂ + m₃ = N) :
    N^2 / 3 ≤ m₁^2 + m₂^2 + m₃^2 := by
  subst hsum
  nlinarith [sq_nonneg (m₁ - m₂), sq_nonneg (m₂ - m₃), sq_nonneg (m₁ - m₃)]

end Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_L9

section Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN6

open Problem97 Problem97.CGN

/- Fragment from Erdos9796Proof.P97.CGN.CGN6; source SHA-256 87eeea2860c10b6c484c3d7aec9f295605a553c9956e5cc04bbc649402bc9c30 -/


/-!
# CGN6: normalized minor-cap chain model

This file starts the CGN6 layer named in the updated counterexample-card-ge-nine
prose. It records the normalized minor-cap chain data the prose uses for the
CGN6b slope-product argument: ordered coordinates, endpoint normalization, the
unit-disk bound, and the adjacent-slope bookkeeping.

The actual geometric construction of this model from a concrete MEC cap packet
is still separate. This file only provides the data interface the subsequent
CGN6b / CGN6c proofs will consume.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped BigOperators


























/- ### CGN6norm scaffold

The prose normalization theorem uses an explicit coordinate frame
centered at the chord midpoint and aligned with the chord / inward
normal directions.  The full packet-to-frame bridge is still separate;
this helper records the coordinate map in the exact algebraic form used
by the prose.
-/































-- The normalization proof is large enough to need a higher elaboration budget.






















/-- CGN6e0: a non-base apex does not lie on the subchord line. -/
theorem Problem97.CGN.CGN6e0_apex_not_on_subchordLine
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (hconv : ConvexIndep A) (hmem : ∀ t : Fin m, L.points t ∈ A)
    {r s : Fin m} (hrs : r < s) {a : ℝ²}
    (haA : a ∈ A) (har : a ≠ L.points r) (has : a ≠ L.points s) :
    signedArea2 (L.points r) (L.points s) a ≠ 0 := by
  intro hzero
  have hcol : Collinear ℝ ({L.points r, L.points s, a} : Set ℝ²) := by
    exact (Problem97.signedArea2_eq_zero_iff_collinear
      (L.points r) (L.points s) a).mp hzero
  have hrA : L.points r ∈ A := hmem r
  have hsA : L.points s ∈ A := hmem s
  have hrs' : L.points r ≠ L.points s := by
    intro h
    exact (ne_of_lt hrs) (L.injective h)
  exact hconv.not_three_collinear hrA hsA haA hrs' har.symm has.symm hcol

/-- CGN6e1: each non-base apex lies strictly on one open side of the
subchord line. -/
theorem Problem97.CGN.CGN6e1_apex_side_dichotomy
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (hconv : ConvexIndep A) (hmem : ∀ t : Fin m, L.points t ∈ A)
    {r s : Fin m} (hrs : r < s) {a : ℝ²}
    (haA : a ∈ A) (har : a ≠ L.points r) (has : a ≠ L.points s) :
    0 < signedArea2 (L.points r) (L.points s) a ∨
      signedArea2 (L.points r) (L.points s) a < 0 := by
  rcases lt_trichotomy (signedArea2 (L.points r) (L.points s) a) 0 with
    hneg | hzero | hpos
  · exact Or.inr hneg
  · exfalso
    exact CGN6e0_apex_not_on_subchordLine hconv hmem hrs haA har has hzero
  · exact Or.inl hpos





/-- CGN6e3: two distinct apices force at least one positive subchain side. -/
theorem Problem97.CGN.CGN6e3_exists_subchain_side_apex
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (hconv : ConvexIndep A) (hmem : ∀ t : Fin m, L.points t ∈ A)
    {r s : Fin m} (hrs : r < s) {a b : ℝ²}
    (haA : a ∈ A) (hbA : b ∈ A)
    (hab : a ≠ b)
    (har : a ≠ L.points r) (has : a ≠ L.points s)
    (hbr : b ≠ L.points r) (hbs : b ≠ L.points s)
    (haeq : dist a (L.points r) = dist a (L.points s))
    (hbeq : dist b (L.points r) = dist b (L.points s)) :
    0 < signedArea2 (L.points r) (L.points s) a ∨
      0 < signedArea2 (L.points r) (L.points s) b := by
  rcases CGN6e1_apex_side_dichotomy hconv hmem hrs haA har has with hapos | haneg
  · exact Or.inl hapos
  · rcases CGN6e1_apex_side_dichotomy hconv hmem hrs hbA hbr hbs with hbpos | hbneg
    · exact Or.inr hbpos
    · exfalso
      exact CGN6e2_not_two_apices_on_complementary_side
        hconv hmem hrs haA hbA hab har has hbr hbs haeq hbeq haneg hbneg

/-- CGN6e4: a positive-side apex determines an indexed witness. -/
theorem Problem97.CGN.CGN6e4_positive_side_apex_to_indexed_witness
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (Hord : StrictCapOrder A L)
    {r s : Fin m} (hrs : r < s) {a : ℝ²}
    (haA : a ∈ A)
    (hapos : 0 < signedArea2 (L.points r) (L.points s) a)
    (haeq : dist a (L.points r) = dist a (L.points s)) :
    ∃ j : Fin m, r < j ∧ j < s ∧ L.points j = a ∧
      WitnessesCapEdgeAt L j r s := by
  have hiff :=
    Hord.subchord_open_side_iff_A (r := r) (s := s) hrs (x := a) haA
  rcases hiff.mp hapos with
    ⟨j, hjr, hjs, hjx⟩
  refine ⟨j, hjr, hjs, hjx, ?_⟩
  exact ⟨hjr, hjs, by simpa [hjx] using haeq⟩

/-- CGN6e5: two apices give existence of an indexed witness. -/
theorem Problem97.CGN.CGN6e5_exists_indexedWitness_of_twoApices
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (Hord : StrictCapOrder A L)
    (hconv : ConvexIndep A) (hmem : ∀ t : Fin m, L.points t ∈ A)
    {r s : Fin m} (hrs : r < s) {a b : ℝ²}
    (haA : a ∈ A) (hbA : b ∈ A)
    (hab : a ≠ b)
    (har : a ≠ L.points r) (has : a ≠ L.points s)
    (hbr : b ≠ L.points r) (hbs : b ≠ L.points s)
    (haeq : dist a (L.points r) = dist a (L.points s))
    (hbeq : dist b (L.points r) = dist b (L.points s)) :
    ∃ j : Fin m, WitnessesCapEdgeAt L j r s := by
  rcases CGN6e3_exists_subchain_side_apex hconv hmem hrs haA hbA hab
      har has hbr hbs haeq hbeq with hapos | hbpos
  · rcases CGN6e4_positive_side_apex_to_indexed_witness Hord hrs haA hapos haeq with
      ⟨j, hjr, hjs, hjx, hjw⟩
    exact ⟨j, hjw⟩
  · rcases CGN6e4_positive_side_apex_to_indexed_witness Hord hrs hbA hbpos hbeq with
      ⟨j, hjr, hjs, hjx, hjw⟩
    exact ⟨j, hjw⟩

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN6

section Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_L10c

open Problem97 Problem97.Dumitrescu

/- Fragment from Erdos9796Proof.P97.Dumitrescu.L10c; source SHA-256 5aa520b1c04392498c794459f80b2aa16f92be66b37143939e64f72fc3578c78 -/


/-!
# Dumitrescu L10c: Cauchy–Schwarz finalization

`Problem97.Dumitrescu.sum_sq_minus_one_lower_bound` is the pure arithmetic
step that derives

  `(m₁² − 1) + (m₂² − 1) + (m₃² − 1) ≥ (n² + 6n) / 3`

from the power-mean inequality `L9` (`power_mean_three_caps`) together
with the cap-cardinality sum identity `m₁ + m₂ + m₃ = n + 3`.

## Derivation

L9 gives:  `(n + 3)² / 3 ≤ m₁² + m₂² + m₃²`.

Subtract 3 from both sides:

  `(m₁² − 1) + (m₂² − 1) + (m₃² − 1)`
  `= (m₁² + m₂² + m₃²) − 3`
  `≥ (n + 3)² / 3 − 3`
  `= (n² + 6n + 9) / 3 − 9/3`
  `= (n² + 6n) / 3`.

No geometric content.  All steps are real arithmetic closed by `nlinarith`.

Blueprint obligation: `p97-dumitrescu-l10c-cauchy-schwarz-finalization`.
-/




/-- **Dumitrescu L10c — Cauchy–Schwarz finalization.**

For nonneg reals `m₁, m₂, m₃` with `m₁ + m₂ + m₃ = n + 3`
(the three-cap cardinality sum in the Dumitrescu setting),
the sum of squared caps minus one satisfies

  `(m₁² − 1) + (m₂² − 1) + (m₃² − 1) ≥ (n² + 6n) / 3`.

**Proof.** Apply `power_mean_three_caps` (L9) with `N := n + 3` to get
`(n + 3)² / 3 ≤ m₁² + m₂² + m₃²`, then observe that subtracting 3 from
both sides yields `(n + 3)² / 3 − 3 = (n² + 6n) / 3`; `nlinarith` closes
the resulting linear arithmetic goal. -/
theorem Problem97.Dumitrescu.sum_sq_minus_one_lower_bound
    {m₁ m₂ m₃ n : ℝ}
    (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (h₃ : 0 ≤ m₃)
    (hsum : m₁ + m₂ + m₃ = n + 3) :
    (n ^ 2 + 6 * n) / 3 ≤ (m₁ ^ 2 - 1) + (m₂ ^ 2 - 1) + (m₃ ^ 2 - 1) := by
  have hpm := power_mean_three_caps h₁ h₂ h₃ hsum
  nlinarith [sq_nonneg (n + 3)]

/-- **CGN8b: cap-size Cauchy--Schwarz saving.**

If `m₁ + m₂ + m₃ = n + 3`, then

`((m₁² - 1) + (m₂² - 1) + (m₃² - 1)) / 4 ≥ (n² + 6n) / 12`.

This is just `sum_sq_minus_one_lower_bound` divided by `4`, matching
the prose statement used in CGN8. -/
theorem Problem97.Dumitrescu.cap_size_cauchy_schwarz_saving
    {m₁ m₂ m₃ n : ℝ}
    (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (h₃ : 0 ≤ m₃)
    (hsum : m₁ + m₂ + m₃ = n + 3) :
    (n ^ 2 + 6 * n) / 12 ≤ ((m₁ ^ 2 - 1) + (m₂ ^ 2 - 1) + (m₃ ^ 2 - 1)) / 4 := by
  have h := sum_sq_minus_one_lower_bound h₁ h₂ h₃ hsum
  nlinarith [h]

end Erdos9796CountingFragment_Erdos9796Proof_P97_Dumitrescu_L10c

section Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN8

open Problem97

/- Fragment from Erdos9796Proof.P97.CGN.CGN8; source SHA-256 e0d08238ab808e6b673b9006abffb488ad895fb6cf431ea389289a83884af65d -/


/-!
# CGN8: circumscribed cap upper bound

This module is the circumscribed-branch counting closure from the
counterexample-card-ge-nine prose. It combines the three-cap decomposition,
the CGN4g support-cap packaging, the CGN6/CGN7 cap-local saving, the
intra-cap disjointness lemma, and the cap-size Cauchy-Schwarz bound to
produce the final circumscribed upper bound on `iCount`.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped BigOperators
open Finset



set_option maxHeartbeats 600000 in
-- CGN8 packages three cap extractions, three cap-local savings, and the final
-- finset/cardinality arithmetic in one theorem; elaboration needs a higher cap.

theorem solution
    {A : Finset ℝ²}
    (hne : A.Nonempty)
    (hnoncol : ¬ Collinear ℝ (A : Set ℝ²))
    (hconv : ConvexIndep A)
    (hbd : 3 <= (A.filter (fun p =>
      dist p (Problem97.MEC.mec A hne).center =
        (Problem97.MEC.mec A hne).radius)).card) :
    (iCount A : ℝ) <= ((11 : ℝ) * A.card ^ 2 - 18 * A.card) / 12 := by
  classical
  obtain ⟨a, b, c, haA, hbA, hcA, hab, hbc, hac, haB, hbB, hcB,
      hacute1, hacute2, hacute3⟩ :=
    Problem97.MEC.exists_nonobtuse_circumscribed_triple hne hnoncol hbd
  let MT : Problem97.MEC.MoserTriangle A hne hnoncol :=
    { v1 := a
      v2 := b
      v3 := c
      v1_mem := haA
      v2_mem := hbA
      v3_mem := hcA
      v1_boundary := haB
      v2_boundary := hbB
      v3_boundary := hcB
      case_split := Or.inl ⟨hab, hbc, hac⟩ }
  have hCirc :
      ∃ h12 h23 h13,
        MT.case_split = Or.inl ⟨h12, h23, h13⟩ := by
    exact ⟨hab, hbc, hac, rfl⟩
  let N : Problem97.MEC.NonObtuseCircumscribedMoserTriangle A hne hnoncol :=
    { toMoserTriangle := MT
      inner_at_v1 := hacute1
      inner_at_v2 := hacute2
      inner_at_v3 := hacute3 }
  let M1 : Problem97.MoserTriangle A := MT.toStructural hCirc
  let M2 : Problem97.MoserTriangle A :=
    { v1 := M1.v2
      v2 := M1.v3
      v3 := M1.v1
      v1_mem := M1.v2_mem
      v2_mem := M1.v3_mem
      v3_mem := M1.v1_mem
      v12_ne := M1.v23_ne
      v13_ne := M1.v12_ne.symm
      v23_ne := M1.v13_ne.symm }
  let M3 : Problem97.MoserTriangle A :=
    { v1 := M1.v3
      v2 := M1.v1
      v3 := M1.v2
      v1_mem := M1.v3_mem
      v2_mem := M1.v1_mem
      v3_mem := M1.v2_mem
      v12_ne := M1.v13_ne.symm
      v13_ne := M1.v23_ne.symm
      v23_ne := M1.v12_ne }
  let P1 : Problem97.CircumscribedMECPacket A M1 :=
    Problem97.CircumscribedMECPacket.ofNonObtuse N hCirc
  let P2 : Problem97.CircumscribedMECPacket A M2 :=
    { center := P1.center
      radius := P1.radius
      radius_pos := P1.radius_pos
      moser_on_boundary_1 := P1.moser_on_boundary_2
      moser_on_boundary_2 := P1.moser_on_boundary_3
      moser_on_boundary_3 := P1.moser_on_boundary_1
      inner_at_v1 := P1.inner_at_v2
      inner_at_v2 := P1.inner_at_v3
      inner_at_v3 := P1.inner_at_v1
      disk_contains_A := P1.disk_contains_A }
  let P3 : Problem97.CircumscribedMECPacket A M3 :=
    { center := P1.center
      radius := P1.radius
      radius_pos := P1.radius_pos
      moser_on_boundary_1 := P1.moser_on_boundary_3
      moser_on_boundary_2 := P1.moser_on_boundary_1
      moser_on_boundary_3 := P1.moser_on_boundary_2
      inner_at_v1 := P1.inner_at_v3
      inner_at_v2 := P1.inner_at_v1
      inner_at_v3 := P1.inner_at_v2
      disk_contains_A := P1.disk_contains_A }
  obtain ⟨CP, hsumCP⟩ :=
    Problem97.Dumitrescu.three_cap_decomposition hconv MT hCirc
  obtain ⟨m1, L1, Packet1, Hside1, Hord1, hL1C1⟩ :=
    Problem97.CGN.CGN4g_capData_of_supportCap
      (A := A) (C := CP.C1) (M := M1)
      hconv hnoncol CP.C1_subset
      (fun x hxA => (CP.arc_membership x hxA).1)
      CP.v2_mem_C1 CP.v3_mem_C1 P1 P1.inner_at_v1
  obtain ⟨m2, L2, Packet2, Hside2, Hord2, hL2C2⟩ :=
    Problem97.CGN.CGN4g_capData_of_supportCap
      (A := A) (C := CP.C2) (M := M2)
      hconv hnoncol CP.C2_subset
      (fun x hxA => (CP.arc_membership x hxA).2.1)
      CP.v3_mem_C2 CP.v1_mem_C2 P2 P2.inner_at_v1
  obtain ⟨m3, L3, Packet3, Hside3, Hord3, hL3C3⟩ :=
    Problem97.CGN.CGN4g_capData_of_supportCap
      (A := A) (C := CP.C3) (M := M3)
      hconv hnoncol CP.C3_subset
      (fun x hxA => (CP.arc_membership x hxA).2.2)
      CP.v1_mem_C3 CP.v2_mem_C3 P3 P3.inner_at_v1
  have hmodelNoWitnessCount :
      ∀ {m : ℕ} {L : Problem97.CGN.OrderedCap m},
        Problem97.CGN.MinorCapChainModel L →
          Nat.choose m 2 - (m - 1)^2 / 4 ≤
            ((Problem97.CGN.CapIndexPairs m).filter
              (fun p : Fin m × Fin m => Problem97.CGN.NoCapWitness L p.1 p.2)).card := by
    intro m L Model
    classical
    let W : Finset (Fin m × Fin m) :=
      (Problem97.CGN.CapIndexPairs m).filter
        (fun p : Fin m × Fin m => Problem97.CGN.HasCapWitness L p.1 p.2)
    have hleft :
        ∀ j : Fin m, ∀ {r s t : Fin m},
          Problem97.CGN.WitnessesCapEdgeAt L j r s →
            Problem97.CGN.WitnessesCapEdgeAt L j r t → s = t := by
      intro j r s t hrs hrt
      by_cases hst : s = t
      · exact hst
      · rcases Problem97.CGN.CGN6c_oneSidedDistanceInjective Model with ⟨hlater, _⟩
        rcases lt_or_gt_of_ne hst with hlt | hgt
        · exfalso
          exact hlater hrs.2.1 hlt (by rw [← hrs.2.2, ← hrt.2.2])
        · exfalso
          exact hlater hrt.2.1 hgt (by rw [← hrt.2.2, ← hrs.2.2])
    have hright :
        ∀ j : Fin m, ∀ {r s t : Fin m},
          Problem97.CGN.WitnessesCapEdgeAt L j r s →
            Problem97.CGN.WitnessesCapEdgeAt L j t s → r = t := by
      intro j r s t hrs hts
      by_cases hrt : r = t
      · exact hrt
      · rcases Problem97.CGN.CGN6c_oneSidedDistanceInjective Model with ⟨_, hearlier⟩
        rcases lt_or_gt_of_ne hrt with hlt | hgt
        · exfalso
          exact hearlier hlt hts.1 (by rw [hrs.2.2, hts.2.2])
        · exfalso
          exact hearlier hgt hrs.1 (by rw [hts.2.2, hrs.2.2])
    have hsum :=
      Problem97.CGN.witnessedPairsAt_sum_le_square_div_four L hleft hright
    have hsigma_card :
        (Finset.univ.sigma (fun j : Fin m => Problem97.CGN.WitnessedPairsAt L j)).card =
          ∑ j : Fin m, (Problem97.CGN.WitnessedPairsAt L j).card := by
      induction (Finset.univ : Finset (Fin m)) using Finset.cons_induction with
      | empty =>
          simp
      | @cons a s ha ih =>
          simp [Finset.sigma, ha, ih, Finset.card_disjUnion]
    let T : Finset (Fin m × Fin m × Fin m) :=
      (Finset.univ.sigma (fun j : Fin m => Problem97.CGN.WitnessedPairsAt L j)).image
        (fun z => (z.1, z.2.1, z.2.2))
    let chooseWitness : Fin m × Fin m → Fin m × Fin m × Fin m :=
      fun p =>
        if h : Problem97.CGN.HasCapWitness L p.1 p.2 then
          (Classical.choose h, p.1, p.2)
        else
          (p.1, p.1, p.2)
    have hW_le_T : W.card ≤ T.card := by
      refine Finset.card_le_card_of_injOn chooseWitness ?_ ?_
      · intro p hp
        have hpWitness : Problem97.CGN.HasCapWitness L p.1 p.2 :=
          (Finset.mem_filter.mp hp).2
        have hmemWit :
            p ∈ Problem97.CGN.WitnessedPairsAt L (Classical.choose hpWitness) := by
          exact (Problem97.CGN.mem_WitnessedPairsAt_iff).2
            (Classical.choose_spec hpWitness)
        rw [show chooseWitness p = (Classical.choose hpWitness, p.1, p.2) by
          simp [chooseWitness, hpWitness]]
        refine Finset.mem_image.mpr ?_
        exact ⟨⟨Classical.choose hpWitness, p⟩,
          Finset.mem_sigma.2 ⟨Finset.mem_univ _, hmemWit⟩, rfl⟩
      · intro p hp q hq hEq
        rcases p with ⟨pr, ps⟩
        rcases q with ⟨qr, qs⟩
        have hpWitness : Problem97.CGN.HasCapWitness L pr ps :=
          (Finset.mem_filter.mp hp).2
        have hqWitness : Problem97.CGN.HasCapWitness L qr qs :=
          (Finset.mem_filter.mp hq).2
        have h1 : pr = qr := by
          simpa [chooseWitness, hpWitness, hqWitness] using
            congrArg (fun t : Fin m × Fin m × Fin m => t.2.1) hEq
        have h2 : ps = qs := by
          simpa [chooseWitness, hpWitness, hqWitness] using
            congrArg (fun t : Fin m × Fin m × Fin m => t.2.2) hEq
        exact Prod.ext h1 h2
    have hT_le_sigma :
        T.card ≤ (Finset.univ.sigma (fun j : Fin m => Problem97.CGN.WitnessedPairsAt L j)).card := by
      exact Finset.card_image_le
    have hW_bound : W.card ≤ (m - 1)^2 / 4 := by
      calc
        W.card ≤ T.card := hW_le_T
        _ ≤ (Finset.univ.sigma (fun j : Fin m => Problem97.CGN.WitnessedPairsAt L j)).card :=
          hT_le_sigma
        _ = ∑ j : Fin m, (Problem97.CGN.WitnessedPairsAt L j).card := hsigma_card
        _ ≤ (m - 1)^2 / 4 := hsum
    let N : Finset (Fin m × Fin m) :=
      (Problem97.CGN.CapIndexPairs m).filter
        (fun p : Fin m × Fin m => Problem97.CGN.NoCapWitness L p.1 p.2)
    have hdisj : Disjoint W N := by
      rw [Finset.disjoint_left]
      intro p hpW hpN
      exact (Finset.mem_filter.mp hpN).2 ((Finset.mem_filter.mp hpW).2)
    have hunion : W ∪ N = Problem97.CGN.CapIndexPairs m := by
      ext p
      constructor
      · intro hp
        rcases Finset.mem_union.mp hp with hpW | hpN
        · exact (Finset.mem_filter.mp hpW).1
        · exact (Finset.mem_filter.mp hpN).1
      · intro hp
        by_cases hHas : Problem97.CGN.HasCapWitness L p.1 p.2
        · exact Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_filter.mpr ⟨hp, hHas⟩
        · exact Finset.mem_union.mpr <| Or.inr <|
            Finset.mem_filter.mpr ⟨hp, hHas⟩
    have hsplit :
        W.card + N.card =
          (Problem97.CGN.CapIndexPairs m).card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hcap_card : (Problem97.CGN.CapIndexPairs m).card = Nat.choose m 2 := by
      let S : Finset ℝ² := Finset.univ.image L.points
      have himg :
          (Problem97.CGN.CapIndexPairs m).image
              (fun p => Problem97.CGN.edgeAt L p.1 p.2) = S.powersetCard 2 := by
        ext xy
        constructor
        · intro hxy
          rcases Finset.mem_image.mp hxy with ⟨p, hp, rfl⟩
          exact Problem97.CGN.edgeAt_mem_powersetCard (L := L) (A := S)
            (hmem := by
              intro t
              exact Finset.mem_image_of_mem _ (Finset.mem_univ _))
            (hrs := Problem97.CGN.mem_CapIndexPairs.mp hp)
        · intro hxy
          rw [Finset.mem_powersetCard] at hxy
          rcases hxy with ⟨hsub, hcard⟩
          rw [Finset.card_eq_two] at hcard
          rcases hcard with ⟨x, y, hxyne, rfl⟩
          have hxS : x ∈ S := hsub (by simp)
          have hyS : y ∈ S := hsub (by simp)
          rcases Finset.mem_image.mp hxS with ⟨i, _, rfl⟩
          rcases Finset.mem_image.mp hyS with ⟨j, _, hj⟩
          have hijne : i ≠ j := by
            intro hij
            apply hxyne
            simpa [hij] using hj
          rcases lt_or_gt_of_ne hijne with hijlt | hjilt
          · refine Finset.mem_image.mpr
              ⟨(i, j), Problem97.CGN.mem_CapIndexPairs.mpr hijlt, ?_⟩
            simpa [Problem97.CGN.edgeAt, hj] using rfl
          · refine Finset.mem_image.mpr
              ⟨(j, i), Problem97.CGN.mem_CapIndexPairs.mpr hjilt, ?_⟩
            simpa [Problem97.CGN.edgeAt, hj, Finset.pair_comm] using rfl
      have hinj :
          Set.InjOn (fun p : Fin m × Fin m => Problem97.CGN.edgeAt L p.1 p.2)
            (Problem97.CGN.CapIndexPairs m) := by
        intro p hp q hq heq
        exact Problem97.CGN.edgeAt_injective_on_CapIndexPairs
          (L := L) hp hq heq
      calc
        (Problem97.CGN.CapIndexPairs m).card =
            ((Problem97.CGN.CapIndexPairs m).image
              (fun p => Problem97.CGN.edgeAt L p.1 p.2)).card := by
          symm
          exact Finset.card_image_of_injOn hinj
        _ = (S.powersetCard 2).card := by rw [himg]
        _ = Nat.choose m 2 := by
          rw [Finset.card_powersetCard]
          rw [Finset.card_image_of_injective _ L.injective]
          simp
    have hN_lower : Nat.choose m 2 - (m - 1)^2 / 4 ≤ N.card := by
      omega
    simpa [N] using hN_lower
  have hcapSaving :
      ∀ {m : ℕ} {L : Problem97.CGN.OrderedCap m}
        (Packet : Problem97.CGN.MecCapPacket A L)
        (Hside : Problem97.CGN.MinorCapSideHypotheses Packet)
        (Hord : Problem97.CGN.StrictCapOrder A L)
        {C : Finset ℝ²}
        (hLC : Finset.univ.image L.points = C)
        (hCsub : C ⊆ A),
        ∃ S : Finset (Finset ℝ²),
          S ⊆ C.powersetCard 2 ∧
          Nat.choose m 2 - (m - 1)^2 / 4 ≤ S.card ∧
          (∀ xy ∈ S, (Problem97.Dumitrescu.capPairApexes A xy).card ≤ 1) := by
    intro m L Packet Hside Hord C hLC hCsub
    classical
    obtain ⟨T, hT, tau, hModelT⟩ :=
      Problem97.CGN.CGN6norm_minorCapChainModel_of_mecCapPacket Packet Hside Hord
    let N : Finset (Fin m × Fin m) :=
      (Problem97.CGN.CapIndexPairs m).filter
        (fun p : Fin m × Fin m => Problem97.CGN.NoCapWitness (L.map T hT) p.1 p.2)
    let S : Finset (Finset ℝ²) :=
      N.image (fun p => Problem97.CGN.edgeAt L p.1 p.2)
    have hmemC : ∀ t : Fin m, L.points t ∈ C := by
      intro t
      rw [← hLC]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hmemA : ∀ t : Fin m, L.points t ∈ A := by
      intro t
      exact hCsub (hmemC t)
    have hSsub : S ⊆ C.powersetCard 2 := by
      intro xy hxy
      rcases Finset.mem_image.mp hxy with ⟨p, hpN, rfl⟩
      exact Problem97.CGN.edgeAt_mem_powersetCard (L := L) (A := C)
        (hmem := hmemC)
        (hrs := Problem97.CGN.mem_CapIndexPairs.mp (Finset.mem_filter.mp hpN).1)
    have hNcard : N.card = S.card := by
      symm
      refine Finset.card_image_of_injOn ?_
      intro p hp q hq heq
      exact Problem97.CGN.edgeAt_injective_on_CapIndexPairs (L := L)
        ((Finset.mem_filter.mp hp).1) ((Finset.mem_filter.mp hq).1) heq
    have hNlower : Nat.choose m 2 - (m - 1)^2 / 4 ≤ N.card := by
      let ModelT : Problem97.CGN.MinorCapChainModel (L.map T hT) :=
        Classical.choice hModelT
      exact hmodelNoWitnessCount ModelT
    refine ⟨S, hSsub, by simpa [hNcard] using hNlower, ?_⟩
    intro xy hxy
    rcases Finset.mem_image.mp hxy with ⟨p, hpN, hxyEq⟩
    rcases p with ⟨r, s⟩
    have hrs : r < s :=
      Problem97.CGN.mem_CapIndexPairs.mp (Finset.mem_filter.mp hpN).1
    subst hxyEq
    by_contra hle
    have hgt : 1 < (Problem97.Dumitrescu.capPairApexes A
        (Problem97.CGN.edgeAt L r s)).card := by
      exact Nat.lt_of_not_ge hle
    have h2 : 2 ≤ (Problem97.Dumitrescu.capPairApexes A
        (Problem97.CGN.edgeAt L r s)).card := by
      exact Nat.succ_le_of_lt hgt
    rcases Problem97.CGN.two_mem_capPairApexes_of_two_le_card
        (L := L) (A := A) (r := r) (s := s) h2 with
      ⟨a, b, hab, ha, hb⟩
    have ha' := Problem97.CGN.capPairApexes_mem_edgeAt_packet
        (L := L) (A := A) (r := r) (s := s) (a := a) ha
    have hb' := Problem97.CGN.capPairApexes_mem_edgeAt_packet
        (L := L) (A := A) (r := r) (s := s) (a := b) hb
    rcases ha' with ⟨haA, har, has, haeq⟩
    rcases hb' with ⟨hbA, hbr, hbs, hbeq⟩
    rcases Problem97.CGN.CGN6e5_exists_indexedWitness_of_twoApices
        (Hord := Hord) (hconv := hconv) (hmem := hmemA)
        (hrs := hrs) (a := a) (b := b)
        haA hbA hab har has hbr hbs haeq hbeq with
      ⟨j, hj⟩
    have hTdist :
        dist ((L.map T hT).points j) ((L.map T hT).points r) =
          dist ((L.map T hT).points j) ((L.map T hT).points s) := by
      have hjdist :=
        (tau.dist_eq_iff (L.points j) (L.points r) (L.points s)).2 hj.2.2
      simpa [Problem97.CGN.OrderedCap.map_points] using hjdist
    have hpNo : Problem97.CGN.NoCapWitness (L.map T hT) r s :=
      (Finset.mem_filter.mp hpN).2
    exact hpNo ⟨j, hj.1, hj.2.1, hTdist⟩
  obtain ⟨S1, hS1sub, hS1lower, hS1save⟩ :=
    hcapSaving Packet1 Hside1 Hord1 hL1C1 CP.C1_subset
  obtain ⟨S2, hS2sub, hS2lower, hS2save⟩ :=
    hcapSaving Packet2 Hside2 Hord2 hL2C2 CP.C2_subset
  obtain ⟨S3, hS3sub, hS3lower, hS3save⟩ :=
    hcapSaving Packet3 Hside3 Hord3 hL3C3 CP.C3_subset
  have hC1subA : CP.C1.powersetCard 2 ⊆ A.powersetCard 2 := by
    intro xy hxy
    rw [Finset.mem_powersetCard] at hxy ⊢
    exact ⟨hxy.1.trans CP.C1_subset, hxy.2⟩
  have hC2subA : CP.C2.powersetCard 2 ⊆ A.powersetCard 2 := by
    intro xy hxy
    rw [Finset.mem_powersetCard] at hxy ⊢
    exact ⟨hxy.1.trans CP.C2_subset, hxy.2⟩
  have hC3subA : CP.C3.powersetCard 2 ⊆ A.powersetCard 2 := by
    intro xy hxy
    rw [Finset.mem_powersetCard] at hxy ⊢
    exact ⟨hxy.1.trans CP.C3_subset, hxy.2⟩
  have hS1subA : S1 ⊆ A.powersetCard 2 := fun _ hx => hC1subA (hS1sub hx)
  have hS2subA : S2 ⊆ A.powersetCard 2 := fun _ hx => hC2subA (hS2sub hx)
  have hS3subA : S3 ⊆ A.powersetCard 2 := fun _ hx => hC3subA (hS3sub hx)
  have hdisjCaps := Problem97.Dumitrescu.cgn8a_intraCapBasePairs_disjoint CP
  have hS12 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro xy hx1 hx2
    exact (Finset.disjoint_left.mp hdisjCaps.1) (hS1sub hx1) (hS2sub hx2)
  have hS13 : Disjoint S1 S3 := by
    rw [Finset.disjoint_left]
    intro xy hx1 hx3
    exact (Finset.disjoint_left.mp hdisjCaps.2.1) (hS1sub hx1) (hS3sub hx3)
  have hS23 : Disjoint S2 S3 := by
    rw [Finset.disjoint_left]
    intro xy hx2 hx3
    exact (Finset.disjoint_left.mp hdisjCaps.2.2) (hS2sub hx2) (hS3sub hx3)
  let S : Finset (Finset ℝ²) := (S1 ∪ S2) ∪ S3
  have hSsubA : S ⊆ A.powersetCard 2 := by
    intro xy hxy
    rcases Finset.mem_union.mp hxy with hx12 | hx3
    · rcases Finset.mem_union.mp hx12 with hx1 | hx2
      · exact hS1subA hx1
      · exact hS2subA hx2
    · exact hS3subA hx3
  have hSsave : ∀ xy ∈ S, (Problem97.Dumitrescu.capPairApexes A xy).card ≤ 1 := by
    intro xy hxy
    rcases Finset.mem_union.mp hxy with hx12 | hx3
    · rcases Finset.mem_union.mp hx12 with hx1 | hx2
      · exact hS1save xy hx1
      · exact hS2save xy hx2
    · exact hS3save xy hx3
  have hSdisj12_3 : Disjoint (S1 ∪ S2) S3 := by
    rw [Finset.disjoint_left]
    intro xy hxy12 hxy3
    rcases Finset.mem_union.mp hxy12 with hx1 | hx2
    · exact (Finset.disjoint_left.mp hS13) hx1 hxy3
    · exact (Finset.disjoint_left.mp hS23) hx2 hxy3
  have hSdisj1_23 : Disjoint S1 (S2 ∪ S3) := by
    rw [Finset.disjoint_left]
    intro xy hx1 hxy23
    rcases Finset.mem_union.mp hxy23 with hx2 | hx3
    · exact (Finset.disjoint_left.mp hS12) hx1 hx2
    · exact (Finset.disjoint_left.mp hS13) hx1 hx3
  have hS_card : S.card = S1.card + S2.card + S3.card := by
    calc
      S.card = S1.card + (S2 ∪ S3).card := by
        simpa [S] using (Finset.card_union_of_disjoint hSdisj1_23)
      _ = S1.card + (S2.card + S3.card) := by
        rw [Finset.card_union_of_disjoint hS23]
      _ = S1.card + S2.card + S3.card := by omega
  have hpair_bound :
      ∀ xy ∈ A.powersetCard 2, (Problem97.Dumitrescu.capPairApexes A xy).card ≤ 2 := by
    intro xy hxy
    rw [Finset.mem_powersetCard] at hxy
    exact Problem97.Dumitrescu.capPairApexes_card_le_two hconv hxy.1 hxy.2
  have hfilterS : (A.powersetCard 2).filter (fun xy => xy ∈ S) = S := by
    ext xy
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).2
    · intro h
      exact Finset.mem_filter.mpr ⟨hSsubA h, h⟩
  have hupper_nat : iCount A + S.card ≤ 2 * (A.powersetCard 2).card := by
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not
        (s := A.powersetCard 2) (p := fun xy => xy ∈ S)
        (f := fun xy => (Problem97.Dumitrescu.capPairApexes A xy).card)
    have hsumS :
        Finset.sum S (fun xy => (Problem97.Dumitrescu.capPairApexes A xy).card) ≤ S.card := by
      calc
        Finset.sum S (fun xy => (Problem97.Dumitrescu.capPairApexes A xy).card)
            ≤ Finset.sum S (fun _xy => 1) := by
              exact Finset.sum_le_sum (fun xy hxy => hSsave xy hxy)
        _ = S.card := by simp
    have hsumNot :
        Finset.sum ((A.powersetCard 2) \ S)
            (fun xy => (Problem97.Dumitrescu.capPairApexes A xy).card) ≤
          2 * ((A.powersetCard 2) \ S).card := by
      calc
        Finset.sum ((A.powersetCard 2) \ S)
            (fun xy => (Problem97.Dumitrescu.capPairApexes A xy).card)
            ≤ Finset.sum ((A.powersetCard 2) \ S) (fun _xy => 2) := by
              exact Finset.sum_le_sum (fun xy hxy => hpair_bound xy (by
                exact (Finset.mem_sdiff.mp hxy).1))
        _ = 2 * ((A.powersetCard 2) \ S).card := by
          simp [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]
    have hmain :
        Finset.sum S (fun xy => (Problem97.Dumitrescu.capPairApexes A xy).card) +
          Finset.sum ((A.powersetCard 2) \ S)
            (fun xy => (Problem97.Dumitrescu.capPairApexes A xy).card)
          ≤ S.card + 2 * ((A.powersetCard 2) \ S).card := by
      exact add_le_add hsumS hsumNot
    have hdisj_cover : Disjoint S ((A.powersetCard 2) \ S) := by
      rw [Finset.disjoint_left]
      intro xy hxS hxsdiff
      exact (Finset.mem_sdiff.mp hxsdiff).2 hxS
    have hcover :
        S ∪ ((A.powersetCard 2) \ S) = A.powersetCard 2 := by
      ext xy
      constructor
      · intro hxy
        rcases Finset.mem_union.mp hxy with hxS | hxsdiff
        · exact hSsubA hxS
        · exact (Finset.mem_sdiff.mp hxsdiff).1
      · intro hxy
        by_cases hxS : xy ∈ S
        · exact Finset.mem_union.mpr (Or.inl hxS)
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxy, hxS⟩))
    have hcard_cover :
        S.card + ((A.powersetCard 2) \ S).card = (A.powersetCard 2).card := by
      rw [← Finset.card_union_of_disjoint hdisj_cover, hcover]
    have hsplit_sum :
        iCount A =
          Finset.sum S (fun xy => (Problem97.Dumitrescu.capPairApexes A xy).card) +
            Finset.sum ((A.powersetCard 2) \ S)
              (fun xy => (Problem97.Dumitrescu.capPairApexes A xy).card) := by
      rw [Problem97.Dumitrescu.iCount_eq_sum_capPairApexes, ← hsplit, hfilterS,
        Finset.filter_notMem_eq_sdiff]
    have hmain' : iCount A ≤ S.card + 2 * ((A.powersetCard 2) \ S).card := by
      rw [hsplit_sum]
      exact hmain
    have hupper_nat_rhs :
        iCount A + S.card ≤ (S.card + 2 * ((A.powersetCard 2) \ S).card) + S.card := by
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hmain' S.card
    have hupper_nat_mid :
        iCount A + S.card ≤ 2 * (S.card + ((A.powersetCard 2) \ S).card) := by
      exact le_trans hupper_nat_rhs (by omega)
    simpa [hcard_cover] using hupper_nat_mid
  have hupper_real :
      (iCount A : ℝ) + (S.card : ℝ) ≤ (A.card : ℝ) * (A.card - 1) := by
    have hnat_real : (iCount A : ℝ) + (S.card : ℝ) ≤ ((2 * (A.powersetCard 2).card : ℕ) : ℝ) := by
      exact_mod_cast hupper_nat
    have hpow_card : ((2 * (A.powersetCard 2).card : ℕ) : ℝ) =
        (A.card : ℝ) * (A.card - 1) := by
      rw [Finset.card_powersetCard, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_choose_two]
      ring
    calc
      (iCount A : ℝ) + (S.card : ℝ) ≤ ((2 * (A.powersetCard 2).card : ℕ) : ℝ) := hnat_real
      _ = (A.card : ℝ) * (A.card - 1) := hpow_card
  have hC1card : CP.C1.card = m1 := by
    rw [← hL1C1, Finset.card_image_of_injective _ L1.injective]
    simp
  have hC2card : CP.C2.card = m2 := by
    rw [← hL2C2, Finset.card_image_of_injective _ L2.injective]
    simp
  have hC3card : CP.C3.card = m3 := by
    rw [← hL3C3, Finset.card_image_of_injective _ L3.injective]
    simp
  have hC1_ge_two : 2 ≤ CP.C1.card := by
    have hsubset : ({M1.v2, M1.v3} : Finset ℝ²) ⊆ CP.C1 := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact CP.v2_mem_C1
      · exact CP.v3_mem_C1
    have hpair : ({M1.v2, M1.v3} : Finset ℝ²).card = 2 := by
      simp [M1.v23_ne]
    have hcard_le : ({M1.v2, M1.v3} : Finset ℝ²).card ≤ CP.C1.card := Finset.card_le_card hsubset
    omega
  have hC2_ge_two : 2 ≤ CP.C2.card := by
    have hsubset : ({M1.v3, M1.v1} : Finset ℝ²) ⊆ CP.C2 := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact CP.v3_mem_C2
      · exact CP.v1_mem_C2
    have hpair : ({M1.v3, M1.v1} : Finset ℝ²).card = 2 := by
      simp [M1.v13_ne.symm]
    have hcard_le : ({M1.v3, M1.v1} : Finset ℝ²).card ≤ CP.C2.card := Finset.card_le_card hsubset
    omega
  have hC3_ge_two : 2 ≤ CP.C3.card := by
    have hsubset : ({M1.v1, M1.v2} : Finset ℝ²) ⊆ CP.C3 := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact CP.v1_mem_C3
      · exact CP.v2_mem_C3
    have hpair : ({M1.v1, M1.v2} : Finset ℝ²).card = 2 := by
      simp [M1.v12_ne]
    have hcard_le : ({M1.v1, M1.v2} : Finset ℝ²).card ≤ CP.C3.card := Finset.card_le_card hsubset
    omega
  have hm1_pos : 1 ≤ m1 := by
    omega
  have hm2_pos : 1 ≤ m2 := by
    omega
  have hm3_pos : 1 ≤ m3 := by
    omega
  have hsave1_real : ((m1 : ℝ)^2 - 1) / 4 ≤ (S1.card : ℝ) := by
    have hnat_real : (((Nat.choose m1 2 - (m1 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (S1.card : ℝ) := by
      exact_mod_cast hS1lower
    have hsub_nat : (m1 - 1)^2 / 4 ≤ Nat.choose m1 2 := by
      rw [Nat.choose_two_right]
      have hsq : (m1 - 1)^2 ≤ m1 * (m1 - 1) := by
        calc
          (m1 - 1)^2 = (m1 - 1) * (m1 - 1) := by ring
          _ ≤ m1 * (m1 - 1) := Nat.mul_le_mul_right (m1 - 1) (Nat.sub_le _ _)
      have hdiv1 : (m1 - 1)^2 / 4 ≤ (m1 * (m1 - 1)) / 4 := Nat.div_le_div_right hsq
      have hdiv2 : (m1 * (m1 - 1)) / 4 ≤ (m1 * (m1 - 1)) / 2 := by
        exact Nat.div_le_div_left (by decide : 2 ≤ 4) (by decide : 0 < 2)
      exact Nat.le_trans hdiv1 hdiv2
    have hcast_sub :
        (((Nat.choose m1 2 - (m1 - 1)^2 / 4 : ℕ) : ℝ)) =
          ((Nat.choose m1 2 : ℕ) : ℝ) - ((((m1 - 1)^2 / 4 : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hsub_nat]
    have hchoose : ((Nat.choose m1 2 : ℕ) : ℝ) = (m1 : ℝ) * (m1 - 1) / 2 := by
      simpa using (Nat.cast_choose_two (K := ℝ) m1)
    have hdiv :
        ((((m1 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (((m1 : ℝ) - 1)^2) / 4 := by
      calc
        ((((m1 - 1)^2 / 4 : ℕ) : ℝ)) ≤ ((((m1 - 1)^2 : ℕ) : ℝ) / 4) := by
          simpa using
            (Nat.cast_div_le (m := (m1 - 1)^2) (n := 4) :
              ((((m1 - 1)^2 / 4 : ℕ) : ℝ)) ≤ ((((m1 - 1)^2 : ℕ) : ℝ) / 4))
        _ = (((m1 : ℝ) - 1)^2) / 4 := by
          rw [Nat.cast_pow, Nat.cast_sub hm1_pos, Nat.cast_one]
    have htmp :
        ((Nat.choose m1 2 : ℕ) : ℝ) - ((((m1 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (S1.card : ℝ) := by
      rw [← hcast_sub]
      exact hnat_real
    have hmain :
        (m1 : ℝ) * (m1 - 1) / 2 - (((m1 : ℝ) - 1)^2) / 4 ≤ (S1.card : ℝ) := by
      have hbridge :
          (m1 : ℝ) * (m1 - 1) / 2 - (((m1 : ℝ) - 1)^2) / 4 ≤
            ((Nat.choose m1 2 : ℕ) : ℝ) - ((((m1 - 1)^2 / 4 : ℕ) : ℝ)) := by
        rw [hchoose]
        gcongr
      exact le_trans hbridge htmp
    have hEq :
        (m1 : ℝ) * (m1 - 1) / 2 - (((m1 : ℝ) - 1)^2) / 4 =
          ((m1 : ℝ)^2 - 1) / 4 := by
      ring
    simpa [hEq] using hmain
  have hsave2_real : ((m2 : ℝ)^2 - 1) / 4 ≤ (S2.card : ℝ) := by
    have hnat_real : (((Nat.choose m2 2 - (m2 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (S2.card : ℝ) := by
      exact_mod_cast hS2lower
    have hsub_nat : (m2 - 1)^2 / 4 ≤ Nat.choose m2 2 := by
      rw [Nat.choose_two_right]
      have hsq : (m2 - 1)^2 ≤ m2 * (m2 - 1) := by
        calc
          (m2 - 1)^2 = (m2 - 1) * (m2 - 1) := by ring
          _ ≤ m2 * (m2 - 1) := Nat.mul_le_mul_right (m2 - 1) (Nat.sub_le _ _)
      have hdiv1 : (m2 - 1)^2 / 4 ≤ (m2 * (m2 - 1)) / 4 := Nat.div_le_div_right hsq
      have hdiv2 : (m2 * (m2 - 1)) / 4 ≤ (m2 * (m2 - 1)) / 2 := by
        exact Nat.div_le_div_left (by decide : 2 ≤ 4) (by decide : 0 < 2)
      exact Nat.le_trans hdiv1 hdiv2
    have hcast_sub :
        (((Nat.choose m2 2 - (m2 - 1)^2 / 4 : ℕ) : ℝ)) =
          ((Nat.choose m2 2 : ℕ) : ℝ) - ((((m2 - 1)^2 / 4 : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hsub_nat]
    have hchoose : ((Nat.choose m2 2 : ℕ) : ℝ) = (m2 : ℝ) * (m2 - 1) / 2 := by
      simpa using (Nat.cast_choose_two (K := ℝ) m2)
    have hdiv :
        ((((m2 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (((m2 : ℝ) - 1)^2) / 4 := by
      calc
        ((((m2 - 1)^2 / 4 : ℕ) : ℝ)) ≤ ((((m2 - 1)^2 : ℕ) : ℝ) / 4) := by
          simpa using
            (Nat.cast_div_le (m := (m2 - 1)^2) (n := 4) :
              ((((m2 - 1)^2 / 4 : ℕ) : ℝ)) ≤ ((((m2 - 1)^2 : ℕ) : ℝ) / 4))
        _ = (((m2 : ℝ) - 1)^2) / 4 := by
          rw [Nat.cast_pow, Nat.cast_sub hm2_pos, Nat.cast_one]
    have htmp :
        ((Nat.choose m2 2 : ℕ) : ℝ) - ((((m2 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (S2.card : ℝ) := by
      rw [← hcast_sub]
      exact hnat_real
    have hmain :
        (m2 : ℝ) * (m2 - 1) / 2 - (((m2 : ℝ) - 1)^2) / 4 ≤ (S2.card : ℝ) := by
      have hbridge :
          (m2 : ℝ) * (m2 - 1) / 2 - (((m2 : ℝ) - 1)^2) / 4 ≤
            ((Nat.choose m2 2 : ℕ) : ℝ) - ((((m2 - 1)^2 / 4 : ℕ) : ℝ)) := by
        rw [hchoose]
        gcongr
      exact le_trans hbridge htmp
    have hEq :
        (m2 : ℝ) * (m2 - 1) / 2 - (((m2 : ℝ) - 1)^2) / 4 =
          ((m2 : ℝ)^2 - 1) / 4 := by
      ring
    simpa [hEq] using hmain
  have hsave3_real : ((m3 : ℝ)^2 - 1) / 4 ≤ (S3.card : ℝ) := by
    have hnat_real : (((Nat.choose m3 2 - (m3 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (S3.card : ℝ) := by
      exact_mod_cast hS3lower
    have hsub_nat : (m3 - 1)^2 / 4 ≤ Nat.choose m3 2 := by
      rw [Nat.choose_two_right]
      have hsq : (m3 - 1)^2 ≤ m3 * (m3 - 1) := by
        calc
          (m3 - 1)^2 = (m3 - 1) * (m3 - 1) := by ring
          _ ≤ m3 * (m3 - 1) := Nat.mul_le_mul_right (m3 - 1) (Nat.sub_le _ _)
      have hdiv1 : (m3 - 1)^2 / 4 ≤ (m3 * (m3 - 1)) / 4 := Nat.div_le_div_right hsq
      have hdiv2 : (m3 * (m3 - 1)) / 4 ≤ (m3 * (m3 - 1)) / 2 := by
        exact Nat.div_le_div_left (by decide : 2 ≤ 4) (by decide : 0 < 2)
      exact Nat.le_trans hdiv1 hdiv2
    have hcast_sub :
        (((Nat.choose m3 2 - (m3 - 1)^2 / 4 : ℕ) : ℝ)) =
          ((Nat.choose m3 2 : ℕ) : ℝ) - ((((m3 - 1)^2 / 4 : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hsub_nat]
    have hchoose : ((Nat.choose m3 2 : ℕ) : ℝ) = (m3 : ℝ) * (m3 - 1) / 2 := by
      simpa using (Nat.cast_choose_two (K := ℝ) m3)
    have hdiv :
        ((((m3 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (((m3 : ℝ) - 1)^2) / 4 := by
      calc
        ((((m3 - 1)^2 / 4 : ℕ) : ℝ)) ≤ ((((m3 - 1)^2 : ℕ) : ℝ) / 4) := by
          simpa using
            (Nat.cast_div_le (m := (m3 - 1)^2) (n := 4) :
              ((((m3 - 1)^2 / 4 : ℕ) : ℝ)) ≤ ((((m3 - 1)^2 : ℕ) : ℝ) / 4))
        _ = (((m3 : ℝ) - 1)^2) / 4 := by
          rw [Nat.cast_pow, Nat.cast_sub hm3_pos, Nat.cast_one]
    have htmp :
        ((Nat.choose m3 2 : ℕ) : ℝ) - ((((m3 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (S3.card : ℝ) := by
      rw [← hcast_sub]
      exact hnat_real
    have hmain :
        (m3 : ℝ) * (m3 - 1) / 2 - (((m3 : ℝ) - 1)^2) / 4 ≤ (S3.card : ℝ) := by
      have hbridge :
          (m3 : ℝ) * (m3 - 1) / 2 - (((m3 : ℝ) - 1)^2) / 4 ≤
            ((Nat.choose m3 2 : ℕ) : ℝ) - ((((m3 - 1)^2 / 4 : ℕ) : ℝ)) := by
        rw [hchoose]
        gcongr
      exact le_trans hbridge htmp
    have hEq :
        (m3 : ℝ) * (m3 - 1) / 2 - (((m3 : ℝ) - 1)^2) / 4 =
          ((m3 : ℝ)^2 - 1) / 4 := by
      ring
    simpa [hEq] using hmain
  have hS_card_real :
      (S.card : ℝ) = (S1.card : ℝ) + (S2.card : ℝ) + (S3.card : ℝ) := by
    exact_mod_cast hS_card
  have hsum_m_nat : m1 + m2 + m3 = A.card + 3 := by
    simpa [hC1card, hC2card, hC3card] using hsumCP
  have hsum_m :
      (m1 : ℝ) + (m2 : ℝ) + (m3 : ℝ) = A.card + 3 := by
    have hsum_m_cast := congrArg (fun n : ℕ => (n : ℝ)) hsum_m_nat
    simpa using hsum_m_cast
  have hsave_total :
      ((A.card : ℝ)^2 + 6 * A.card) / 12 ≤ (S.card : ℝ) := by
    have hcs := Problem97.Dumitrescu.cap_size_cauchy_schwarz_saving
      (show (0 : ℝ) ≤ m1 by exact_mod_cast Nat.zero_le m1)
      (show (0 : ℝ) ≤ m2 by exact_mod_cast Nat.zero_le m2)
      (show (0 : ℝ) ≤ m3 by exact_mod_cast Nat.zero_le m3)
      hsum_m
    have hsavesum :
        (((m1 : ℝ)^2 - 1) + ((m2 : ℝ)^2 - 1) + ((m3 : ℝ)^2 - 1)) / 4
          ≤ (S1.card : ℝ) + (S2.card : ℝ) + (S3.card : ℝ) := by
      nlinarith [hsave1_real, hsave2_real, hsave3_real]
    rw [hS_card_real]
    exact le_trans hcs hsavesum
  nlinarith [hupper_real, hsave_total]

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN8
