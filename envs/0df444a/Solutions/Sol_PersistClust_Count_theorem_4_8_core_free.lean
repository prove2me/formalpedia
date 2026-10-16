-- Prove2me | solution 1 for PersistClust.Count.theorem_4_8_core_free
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-16T05:30:31.966663+00:00
-- url     : https://prove2.me/submissions/7b390829-c912-4c06-817f-e1d75eb98ac5

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Theorems.Thm_PersistClust_Count_proof_thm_4_8_algorithm_output
import Theorems.Thm_PersistClust_Count_proof_thm_4_8_partition_count

/-!
# Theorem 4.8 — deterministic correctness core (pure assembly)

The statement is the published `PersistClust.Count.theorem_4_8_core`: on a netted sample with
positive sample values, τ-generic Rips-critical structure, and a Theorem-4.5 multi-bijection,
Procedure 1's cluster count is exactly the number of `d₂`-prominent peaks of `D₀f`, for every
sort order.

The proof is pure assembly of the two already-proved children of the 4.8 milestone:

1. `proof_thm_4_8_algorithm_output` (M4): `numClusters g Dm δ τ σ` equals the multiplicity of
   the closed `τ`-window `{q | q.2 < D q.1 ∧ q.1.2 ≤ q.1.1 − τ ∧ τ ≤ q.1.1}` of the `n`-point
   Rips diagram `ripsDiagram (dist∘pts) (f∘pts) δ`.

2. `proof_thm_4_8_partition_count` (M3): the multiplicity of the window
   `Δ^S_τ ∩ Λ^E_τ` of the L-side Rips diagram equals `prominentCount (diagram0 f) d₂`, under
   the Theorem-4.5 multi-bijection `γ` (for `IsDiagramLike` of both sides) and separation.

The bridge between the two children:

* **`L_dup`** (inlined below, `Aux.ldup_ripsDiagram_eq`): the `n`-point Rips diagram and the
  `L`-side (deduplicated) Rips diagram are *equal* — duplicates are `δ`-adjacent at distance
  `0` and share stage membership, so every level's Rips components of the sample are the
  pullback of the `L`-side components along the sample→`L` map.

* **Region reconciliation** (the one real step): the M4 window differs from `Δ^S_τ ∩ Λ^E_τ`
  only through `τ ≤ b` vs `τ < b` — bars born exactly at `τ` with death `≤ birth − τ = 0`.
  The hypothesis `hτexc` says the sample's Rips diagram has multiplicity `0` there, so no
  copy exists in that edge region and the two copy sets are equal.
-/

open MeasureTheory Bundle
open scoped ContDiff Manifold

namespace PersistClust.Count

/-! ## Inlined green pieces

Three small lemmas from the ACCEPTED `theorem_4_5` solution (the `FiltrationLaw` of the
upper-star Rips filtration and its symmetry helpers) and `t45gamma_isDiagramLike_mult`
(`mult r` is always diagram-like), followed by the green `L_dup` duplicate-vertex bridge
(`Aux.ldup_ripsDiagram_eq`). They are inlined because scratch/solution-internal lemmas are
not importable into this module. -/

namespace Aux

/-- `ReflTransGen` of a symmetric relation is symmetric (tail-step induction). -/
theorem t45gamma_rtgen_symm {ι : Type*} {R : ι → ι → Prop}
    (hsym : ∀ a b, R a b → R b a) {i j : ι} (h : Relation.ReflTransGen R i j) :
    Relation.ReflTransGen R j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.head (hsym _ _ hbc)

/-- The Rips step relation on level `t` is symmetric (the Rips graph is undirected). -/
theorem t45gamma_RipsRel_symm {ι : Type*} (Dm : ι → ι → ℝ) (g : ι → ℝ) (δ t : ℝ) :
    ∀ a b, (fun a b => t ≤ g a ∧ t ≤ g b ∧ (ripsGraph Dm δ).Adj a b) a b →
      (fun a b => t ≤ g a ∧ t ≤ g b ∧ (ripsGraph Dm δ).Adj a b) b a :=
  fun _ _ ⟨h1, h2, h3⟩ => ⟨h2, h1, h3.symm⟩

/-- The upper-star Rips filtration is a genuine `FiltrationLaw`. -/
theorem t45gamma_rips_filtrationLaw {ι : Type*} (Dm : ι → ι → ℝ) (g : ι → ℝ) (δ : ℝ) :
    FiltrationLaw (fun t => {i | t ≤ g i}) (ripsJoined Dm g δ) where
  antitone := fun s t hst i hi => hst.trans hi
  mem := by
    intro t i j h
    obtain ⟨hgi, hrt⟩ := h
    refine ⟨hgi, ?_⟩
    induction hrt with
    | refl => exact hgi
    | tail _ hbc _ => exact hbc.2.1
  refl := fun t i hi => ⟨hi, Relation.ReflTransGen.refl⟩
  symm := by
    intro t i j h
    obtain ⟨hgi, hrt⟩ := h
    refine ⟨?_, ?_⟩
    · induction hrt with
      | refl => exact hgi
      | tail _ hbc _ => exact hbc.2.1
    · exact t45gamma_rtgen_symm (t45gamma_RipsRel_symm Dm g δ t) hrt
  trans := by
    intro t i j k hij hjk
    obtain ⟨hgi, hrt1⟩ := hij
    obtain ⟨-, hrt2⟩ := hjk
    exact ⟨hgi, Relation.ReflTransGen.trans hrt1 hrt2⟩
  compat := by
    intro s t hst i j h
    obtain ⟨hgi, hrt⟩ := h
    refine ⟨hst.trans hgi, ?_⟩
    induction hrt with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih =>
      exact ih.tail ⟨hst.trans hab.1, hst.trans hab.2.1, hab.2.2⟩

/-- Every `mult r` is diagram-like: off-diagonal multiplicity forces `death < birth`. -/
theorem t45gamma_isDiagramLike_mult (r : ℝ → ℝ → ℕ∞) : IsDiagramLike (mult r) := by
  intro p hp
  by_contra hne
  have hle : p.1 ≤ p.2 := not_lt.mp hne
  have h0 : mult r p = 0 := by
    unfold mult
    by_cases h1 : p.1 ≠ ⊥ ∧ p.1 ≠ ⊤
    · rw [if_pos h1]
      by_cases h2 : p.2 = ⊥
      · have hle' : p.1 ≤ ⊥ := h2 ▸ hle
        exact absurd (le_antisymm hle' bot_le) h1.1
      · rw [if_neg h2]
        by_cases h3 : p.2 < p.1
        · exact absurd h3 (not_lt.mpr hle)
        · rw [if_neg h3]
    · rw [if_neg h1]
  exact hp h0

section
variable {X : Type*} [MetricSpace X] {n : ℕ}

/-! ### `L_dup`: the duplicate-vertex bridge

The root's algorithm runs on `n` samples `pts : Fin n → X` (coordinates may repeat), while
Theorem 4.5's instance uses the deduplicated `L : Finset X` (a SET). Duplicate vertices are
`δ`-adjacent at distance `0` and share stage membership, so at every level the Rips
components of the sample graph are the pullback of the `L`-side components via the
sample→`L` map. Hence the two `ripsDiagram`s are EQUAL. -/

/-- The `n`-sample's induced vertex map into `L` (needs `pts` to land in `L`). -/
def toL (pts : Fin n → X) {L : Finset X} (hmem : ∀ i : Fin n, pts i ∈ L) (i : Fin n) : ↥L :=
  ⟨pts i, hmem i⟩

/-- A chosen lift of each `L`-point (needs every point of `L` to be sampled). -/
noncomputable def dlift (pts : Fin n → X) {L : Finset X}
    (hsurj : ∀ y ∈ (L : Set X), ∃ i : Fin n, pts i = y) (y : ↥L) : Fin n :=
  Classical.choose (hsurj (y : X) y.2)

omit [MetricSpace X] in
theorem dlift_spec (pts : Fin n → X) {L : Finset X}
    (hsurj : ∀ y ∈ (L : Set X), ∃ i : Fin n, pts i = y) (y : ↥L) :
    pts (dlift pts hsurj y) = (y : X) :=
  Classical.choose_spec (hsurj (y : X) y.2)

omit [MetricSpace X] in
theorem toL_dlift (pts : Fin n → X) {L : Finset X} (hmem : ∀ i : Fin n, pts i ∈ L)
    (hsurj : ∀ y ∈ (L : Set X), ∃ i : Fin n, pts i = y) (y : ↥L) :
    toL pts hmem (dlift pts hsurj y) = y :=
  Subtype.ext (dlift_spec pts hsurj y)

omit [MetricSpace X] in
theorem toL_inj (pts : Fin n → X) {L : Finset X} (hmem : ∀ i : Fin n, pts i ∈ L)
    {i j : Fin n} (h : pts i = pts j) : toL pts hmem i = toL pts hmem j :=
  Subtype.ext h

omit [MetricSpace X] in
/-- `toL` is surjective onto `↥L` when `L` is the image of `pts`. -/
theorem toL_surj (pts : Fin n → X) {L : Finset X} (hmem : ∀ i : Fin n, pts i ∈ L)
    (hsurj : ∀ y ∈ (L : Set X), ∃ i : Fin n, pts i = y) (y : ↥L) :
    ∃ i : Fin n, toL pts hmem i = y :=
  ⟨dlift pts hsurj y, toL_dlift pts hmem hsurj y⟩

/-- Two samples at the same underlying point are `δ`-joined at every level they both occupy
(distance `0 ≤ δ`; the reflexive case is `i = j`). -/
theorem same_pts_joined (pts : Fin n → X) (f : X → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (t : ℝ)
    {i j : Fin n} (hij : pts i = pts j) (ht : t ≤ f (pts i)) :
    ripsJoined (fun a b : Fin n => dist (pts a) (pts b)) (fun a : Fin n => f (pts a)) δ t i j := by
  refine ⟨ht, ?_⟩
  rcases eq_or_ne i j with rfl | hne
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single
      ⟨ht, by show t ≤ f (pts j); rw [← hij]; exact ht,
        by simp only [ripsGraph, SimpleGraph.fromRel_adj]
           exact ⟨hne, Or.inl (by rw [hij, dist_self]; exact hδ)⟩⟩

/-- Forward adjacency transfer along `toL` (needs the images to be distinct). -/
theorem adj_toL (pts : Fin n → X) {L : Finset X} (hmem : ∀ i : Fin n, pts i ∈ L) (δ : ℝ)
    {a b : Fin n} (hp : pts a ≠ pts b)
    (h : (ripsGraph (fun i j : Fin n => dist (pts i) (pts j)) δ).Adj a b) :
    (ripsGraph (fun y z : ↥L => dist (y : X) (z : X)) δ).Adj
      (toL pts hmem a) (toL pts hmem b) := by
  simp only [ripsGraph, SimpleGraph.fromRel_adj] at h ⊢
  obtain ⟨-, hrel⟩ := h
  refine ⟨fun heq => hp (Subtype.ext_iff.mp heq), ?_⟩
  rcases hrel with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Backward adjacency transfer along `dlift` (needs the lifts' spec). -/
theorem adj_dlift (pts : Fin n → X) {L : Finset X} (δ : ℝ)
    (hsurj : ∀ y ∈ (L : Set X), ∃ i : Fin n, pts i = y) {y z : ↥L}
    (h : (ripsGraph (fun y z : ↥L => dist (y : X) (z : X)) δ).Adj y z) :
    (ripsGraph (fun i j : Fin n => dist (pts i) (pts j)) δ).Adj
      (dlift pts hsurj y) (dlift pts hsurj z) := by
  simp only [ripsGraph, SimpleGraph.fromRel_adj] at h ⊢
  obtain ⟨hne, hrel⟩ := h
  refine ⟨?_, ?_⟩
  · intro heq
    exact hne (Subtype.ext (by
      have h2 : pts (dlift pts hsurj y) = pts (dlift pts hsurj z) := congrArg pts heq
      rwa [dlift_spec pts hsurj y, dlift_spec pts hsurj z] at h2))
  · rcases hrel with h | h
    · left; rwa [dlift_spec pts hsurj y, dlift_spec pts hsurj z]
    · right; rwa [dlift_spec pts hsurj y, dlift_spec pts hsurj z]

/-- Forward step: an `n`-side Rips step maps to a (possibly reflexive) `L`-side chain step. -/
theorem fwd_step (pts : Fin n → X) {L : Finset X} (f : X → ℝ) (δ : ℝ)
    (hmem : ∀ i : Fin n, pts i ∈ L) (t : ℝ) {a b : Fin n}
    (h : t ≤ f (pts a) ∧ t ≤ f (pts b) ∧
      (ripsGraph (fun i j : Fin n => dist (pts i) (pts j)) δ).Adj a b) :
    Relation.ReflTransGen
      (fun y z : ↥L => t ≤ f (y : X) ∧ t ≤ f (z : X) ∧
        (ripsGraph (fun y z : ↥L => dist (y : X) (z : X)) δ).Adj y z)
      (toL pts hmem a) (toL pts hmem b) := by
  obtain ⟨hta, htb, hadj⟩ := h
  by_cases hp : pts a = pts b
  · rw [toL_inj pts hmem hp]
  · refine Relation.ReflTransGen.single ⟨?_, ?_, adj_toL pts hmem δ hp hadj⟩
    · show t ≤ f (pts a); exact hta
    · show t ≤ f (pts b); exact htb

/-- Forward chain: an `n`-side `ripsJoined`-chain maps to an `L`-side chain. -/
theorem fwd_chain (pts : Fin n → X) {L : Finset X} (f : X → ℝ) (δ : ℝ)
    (hmem : ∀ i : Fin n, pts i ∈ L) (t : ℝ) {i j : Fin n}
    (h : Relation.ReflTransGen
      (fun a b : Fin n => t ≤ f (pts a) ∧ t ≤ f (pts b) ∧
        (ripsGraph (fun i j : Fin n => dist (pts i) (pts j)) δ).Adj a b) i j) :
    Relation.ReflTransGen
      (fun y z : ↥L => t ≤ f (y : X) ∧ t ≤ f (z : X) ∧
        (ripsGraph (fun y z : ↥L => dist (y : X) (z : X)) δ).Adj y z)
      (toL pts hmem i) (toL pts hmem j) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact ih.trans (fwd_step pts f δ hmem t hst)

/-- Backward step: an `L`-side Rips step lifts along `dlift`. -/
theorem bwd_step (pts : Fin n → X) {L : Finset X} (f : X → ℝ) (δ : ℝ)
    (hsurj : ∀ y ∈ (L : Set X), ∃ i : Fin n, pts i = y) (t : ℝ) {y z : ↥L}
    (h : t ≤ f (y : X) ∧ t ≤ f (z : X) ∧
      (ripsGraph (fun y z : ↥L => dist (y : X) (z : X)) δ).Adj y z) :
    t ≤ f (pts (dlift pts hsurj y)) ∧ t ≤ f (pts (dlift pts hsurj z)) ∧
      (ripsGraph (fun i j : Fin n => dist (pts i) (pts j)) δ).Adj
        (dlift pts hsurj y) (dlift pts hsurj z) := by
  obtain ⟨hy, hz, hadj⟩ := h
  refine ⟨?_, ?_, adj_dlift pts δ hsurj hadj⟩
  · rw [dlift_spec pts hsurj y]; exact hy
  · rw [dlift_spec pts hsurj z]; exact hz

/-- Backward chain: an `L`-side chain lifts to an `n`-side chain (`ReflTransGen.lift`). -/
theorem bwd_chain (pts : Fin n → X) {L : Finset X} (f : X → ℝ) (δ : ℝ)
    (hsurj : ∀ y ∈ (L : Set X), ∃ i : Fin n, pts i = y) (t : ℝ) {y z : ↥L}
    (h : Relation.ReflTransGen
      (fun y z : ↥L => t ≤ f (y : X) ∧ t ≤ f (z : X) ∧
        (ripsGraph (fun y z : ↥L => dist (y : X) (z : X)) δ).Adj y z) y z) :
    Relation.ReflTransGen
      (fun a b : Fin n => t ≤ f (pts a) ∧ t ≤ f (pts b) ∧
        (ripsGraph (fun i j : Fin n => dist (pts i) (pts j)) δ).Adj a b)
      (dlift pts hsurj y) (dlift pts hsurj z) :=
  (Relation.ReflTransGen.lift (r := fun y z : ↥L => t ≤ f (y : X) ∧ t ≤ f (z : X) ∧
        (ripsGraph (fun y z : ↥L => dist (y : X) (z : X)) δ).Adj y z)
      (p := fun a b : Fin n => t ≤ f (pts a) ∧ t ≤ f (pts b) ∧
        (ripsGraph (fun i j : Fin n => dist (pts i) (pts j)) δ).Adj a b)
      (dlift pts hsurj) (fun _ _ hab => bwd_step pts f δ hsurj t hab)) y z h

/-- **The component pullback**: at every level `t`, the `n`-sample Rips classes are the
pullback of the `L`-side classes along `toL`. -/
theorem pullback_iff (pts : Fin n → X) {L : Finset X} (f : X → ℝ) (δ : ℝ)
    (hmem : ∀ i : Fin n, pts i ∈ L)
    (hsurj : ∀ y ∈ (L : Set X), ∃ i : Fin n, pts i = y) (hδ : 0 ≤ δ) (t : ℝ) (i j : Fin n) :
    ripsJoined (fun a b : Fin n => dist (pts a) (pts b)) (fun a : Fin n => f (pts a)) δ t i j ↔
      ripsJoined (fun y z : ↥L => dist (y : X) (z : X)) (fun y : ↥L => f (y : X)) δ t
        (toL pts hmem i) (toL pts hmem j) := by
  constructor
  · intro h
    obtain ⟨hmemi, hchain⟩ := h
    refine ⟨?_, fwd_chain pts f δ hmem t hchain⟩
    show t ≤ f (pts i); exact hmemi
  · intro h
    have hmemj : t ≤ f (pts j) := by
      have hmem' := (t45gamma_rips_filtrationLaw (fun y z : ↥L => dist (y : X) (z : X))
        (fun y : ↥L => f (y : X)) δ).mem h
      show t ≤ f (pts j); exact hmem'.2
    obtain ⟨hmemi, hchain⟩ := h
    have hjoin1 : ripsJoined (fun a b : Fin n => dist (pts a) (pts b))
        (fun a : Fin n => f (pts a)) δ t i (dlift pts hsurj (toL pts hmem i)) :=
      same_pts_joined pts f δ hδ t
        (by rw [dlift_spec pts hsurj (toL pts hmem i)]; rfl) hmemi
    have hmem_a : t ≤ f (pts (dlift pts hsurj (toL pts hmem i))) := by
      rw [dlift_spec pts hsurj (toL pts hmem i)]; exact hmemi
    have hjoin2 : ripsJoined (fun a b : Fin n => dist (pts a) (pts b))
        (fun a : Fin n => f (pts a)) δ t
        (dlift pts hsurj (toL pts hmem i)) (dlift pts hsurj (toL pts hmem j)) :=
      ⟨hmem_a, bwd_chain pts f δ hsurj t hchain⟩
    have hjoin3 : ripsJoined (fun a b : Fin n => dist (pts a) (pts b))
        (fun a : Fin n => f (pts a)) δ t (dlift pts hsurj (toL pts hmem j)) j :=
      same_pts_joined pts f δ hδ t
        (by rw [dlift_spec pts hsurj (toL pts hmem j)]; rfl)
        (by rw [dlift_spec pts hsurj (toL pts hmem j)]; exact hmemj)
    exact (t45gamma_rips_filtrationLaw (fun a b : Fin n => dist (pts a) (pts b))
      (fun a : Fin n => f (pts a)) δ).trans
      ((t45gamma_rips_filtrationLaw (fun a b : Fin n => dist (pts a) (pts b))
        (fun a : Fin n => f (pts a)) δ).trans hjoin1 hjoin2) hjoin3

/-- **Class-image identity**: the `toL`-image of an `n`-side class is exactly the `L`-side
class of the image point (uses surjectivity of `toL`). -/
theorem image_cls (pts : Fin n → X) {L : Finset X} (f : X → ℝ) (δ : ℝ)
    (hmem : ∀ i : Fin n, pts i ∈ L)
    (hsurj : ∀ y ∈ (L : Set X), ∃ i : Fin n, pts i = y) (hδ : 0 ≤ δ) (t : ℝ) (i : Fin n) :
    toL pts hmem '' {j : Fin n | ripsJoined (fun a b : Fin n => dist (pts a) (pts b))
        (fun a : Fin n => f (pts a)) δ t i j} =
      {z : ↥L | ripsJoined (fun y z : ↥L => dist (y : X) (z : X)) (fun y : ↥L => f (y : X)) δ t
        (toL pts hmem i) z} := by
  ext z
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact (pullback_iff pts f δ hmem hsurj hδ t i j).mp hj
  · intro hz
    refine ⟨dlift pts hsurj z, ?_, toL_dlift pts hmem hsurj z⟩
    exact (pullback_iff pts f δ hmem hsurj hδ t i (dlift pts hsurj z)).mpr
      (by rwa [toL_dlift pts hmem hsurj z])

/-- **Injectivity** of `S ↦ toL '' S` on the `n`-side class image (from the pullback). -/
theorem injOn_toL_image (pts : Fin n → X) {L : Finset X} (f : X → ℝ) (δ : ℝ)
    (hmem : ∀ i : Fin n, pts i ∈ L)
    (hsurj : ∀ y ∈ (L : Set X), ∃ i : Fin n, pts i = y) (hδ : 0 ≤ δ) (s t : ℝ) :
    Set.InjOn (fun S : Set (Fin n) => toL pts hmem '' S)
      ((fun i : Fin n => {j : Fin n | ripsJoined (fun a b : Fin n => dist (pts a) (pts b))
        (fun a : Fin n => f (pts a)) δ t i j}) '' {i : Fin n | s ≤ f (pts i)}) := by
  rintro S ⟨i, -, rfl⟩ S' ⟨i', -, rfl⟩ hF
  have hF' : toL pts hmem '' {j : Fin n | ripsJoined (fun a b : Fin n => dist (pts a) (pts b))
        (fun a : Fin n => f (pts a)) δ t i j}
      = toL pts hmem '' {j : Fin n | ripsJoined (fun a b : Fin n => dist (pts a) (pts b))
        (fun a : Fin n => f (pts a)) δ t i' j} := hF
  rw [image_cls pts f δ hmem hsurj hδ t i, image_cls pts f δ hmem hsurj hδ t i'] at hF'
  have hpre : ∀ i : Fin n,
      {j : Fin n | ripsJoined (fun a b : Fin n => dist (pts a) (pts b))
          (fun a : Fin n => f (pts a)) δ t i j}
        = toL pts hmem ⁻¹' {z : ↥L | ripsJoined (fun y z : ↥L => dist (y : X) (z : X))
            (fun y : ↥L => f (y : X)) δ t (toL pts hmem i) z} := by
    intro i
    ext j
    rw [Set.mem_preimage]
    exact pullback_iff pts f δ hmem hsurj hδ t i j
  show {j : Fin n | ripsJoined (fun a b : Fin n => dist (pts a) (pts b))
        (fun a : Fin n => f (pts a)) δ t i j}
      = {j : Fin n | ripsJoined (fun a b : Fin n => dist (pts a) (pts b))
        (fun a : Fin n => f (pts a)) δ t i' j}
  rw [hpre i, hpre i', hF']

/-- **`L_dup` (rank form)**: the `n`-point and `L`-point Rips rank functions coincide. -/
theorem ldup_ripsRank_eq (pts : Fin n → X) (L : Finset X) (f : X → ℝ) (δ : ℝ)
    (hmem : ∀ i : Fin n, pts i ∈ L)
    (hsurj : ∀ y ∈ (L : Set X), ∃ i : Fin n, pts i = y) (hδ : 0 ≤ δ) :
    ripsRank (fun a b : Fin n => dist (pts a) (pts b)) (fun a : Fin n => f (pts a)) δ
      = ripsRank (fun y z : ↥L => dist (y : X) (z : X)) (fun y : ↥L => f (y : X)) δ := by
  funext s t
  let An : Set (Set (Fin n)) :=
    (fun i : Fin n => {j : Fin n | ripsJoined (fun a b : Fin n => dist (pts a) (pts b))
      (fun a : Fin n => f (pts a)) δ t i j}) '' {i : Fin n | s ≤ f (pts i)}
  let AL : Set (Set ↥L) :=
    (fun y : ↥L => {z : ↥L | ripsJoined (fun y z : ↥L => dist (y : X) (z : X))
      (fun y : ↥L => f (y : X)) δ t y z}) '' {y : ↥L | s ≤ f (y : X)}
  change An.encard = AL.encard
  have hFAL : (fun S : Set (Fin n) => toL pts hmem '' S) '' An = AL := by
    ext T
    constructor
    · rintro ⟨S, ⟨i, hi, rfl⟩, rfl⟩
      refine ⟨toL pts hmem i, ?_, (image_cls pts f δ hmem hsurj hδ t i).symm⟩
      show s ≤ f (pts i); exact hi
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(fun i : Fin n => {j : Fin n | ripsJoined (fun a b : Fin n => dist (pts a) (pts b))
          (fun a : Fin n => f (pts a)) δ t i j}) (dlift pts hsurj y), ?_, ?_⟩
      · refine ⟨dlift pts hsurj y, ?_, rfl⟩
        show s ≤ f (pts (dlift pts hsurj y)); rw [dlift_spec pts hsurj y]; exact hy
      · show toL pts hmem ''
            {j : Fin n | ripsJoined (fun a b : Fin n => dist (pts a) (pts b))
              (fun a : Fin n => f (pts a)) δ t (dlift pts hsurj y) j}
          = {z : ↥L | ripsJoined (fun y z : ↥L => dist (y : X) (z : X))
              (fun y : ↥L => f (y : X)) δ t y z}
        rw [image_cls pts f δ hmem hsurj hδ t (dlift pts hsurj y), toL_dlift pts hmem hsurj y]
  have hInj : Set.InjOn (fun S : Set (Fin n) => toL pts hmem '' S) An :=
    injOn_toL_image pts f δ hmem hsurj hδ s t
  rw [← hFAL]
  exact hInj.encard_image.symm

/-- **`L_dup` (diagram form)**: the two `ripsDiagram`s are equal. -/
theorem ldup_ripsDiagram_eq (pts : Fin n → X) (L : Finset X) (f : X → ℝ) (δ : ℝ)
    (hmem : ∀ i : Fin n, pts i ∈ L)
    (hsurj : ∀ y ∈ (L : Set X), ∃ i : Fin n, pts i = y) (hδ : 0 ≤ δ) :
    ripsDiagram (fun a b : Fin n => dist (pts a) (pts b)) (fun a : Fin n => f (pts a)) δ
      = ripsDiagram (fun y z : ↥L => dist (y : X) (z : X)) (fun y : ↥L => f (y : X)) δ := by
  unfold ripsDiagram
  rw [ldup_ripsRank_eq pts L f δ hmem hsurj hδ]


/-- **τ-edge exclusion from the matching.** Under a Theorem-4.5 multi-bijection at radius `cδ`
and `(d₁, d₂)`-separation, the target diagram has no point born exactly at a threshold `τ` in
the window `(d₁ + 2cδ, d₂ − 3cδ)` with death `≤ 0`: such a point lies in `Q^SE_{cδ}`, so its
γ-preimage is born within `cδ` of `τ`; separation then puts the preimage in `Q^NE_{cδ}`
(diagonal copies included), and assertion (i) forces the death above `0`. -/
theorem tau_edge_free (D D' : EReal × EReal → ℕ∞) (γ : Copies D ≃ Copies D') (c δ : ℝ)
    (hc : 0 < c) (hδ : 0 < δ) (hγ : SatisfiesIIV γ (c * δ) (c * δ)) (d₁ d₂ : ℝ)
    (hd₁ : 0 ≤ d₁) (hsep : IsSeparated D d₁ d₂) (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ)
    (hτ₂ : τ < d₂ - 3 * c * δ) (d : EReal) (hd : d ≤ ((0 : ℝ) : EReal)) :
    D' (((τ : ℝ) : EReal), d) = 0 := by
  by_contra hne
  have hcδ : (0 : ℝ) < c * δ := mul_pos hc hδ
  let b : Copies D' := Sum.inl ⟨((((τ : ℝ) : EReal), d), 0), by
    rw [Nat.cast_zero]; exact pos_iff_ne_zero.mpr hne⟩
  have hpb : pt b = (((τ : ℝ) : EReal), d) := rfl
  have hbQ : pt b ∈ QSE (c * δ) := by
    rw [hpb]
    exact ⟨EReal.coe_lt_coe_iff.mpr (by linarith),
      le_trans hd (EReal.coe_le_coe_iff.mpr hcδ.le)⟩
  set a := γ.symm b with ha
  have hab : γ a = b := by rw [ha]; exact γ.apply_symm_apply b
  have hcl := hγ.2.2.2 b hbQ
  rw [hpb] at hcl
  obtain ⟨hx1, hx2⟩ := hcl
  -- the birth of `a` is a real number within `cδ` of `τ`
  have hxtop : (pt a).1 ≠ ⊤ := by
    intro h
    rw [h, ← EReal.coe_add] at hx1
    exact absurd hx1 (not_le.mpr (EReal.coe_lt_top _))
  have hxbot : (pt a).1 ≠ ⊥ := by
    intro h
    rw [h, EReal.bot_add] at hx2
    exact absurd hx2 (not_le.mpr (EReal.bot_lt_coe _))
  set xr := (pt a).1.toReal with hxr
  have hxeq : (pt a).1 = ((xr : ℝ) : EReal) := (EReal.coe_toReal hxtop hxbot).symm
  rw [hxeq, ← EReal.coe_add, EReal.coe_le_coe_iff] at hx1 hx2
  -- `pt a ∈ Q^NE_{cδ}`: the death of `a` exceeds `cδ`
  have key : ∀ a' : Copies D, (pt a').1 = ((xr : ℝ) : EReal) →
      ((c * δ : ℝ) : EReal) < (pt a').2 := by
    intro a' hx'
    rcases a' with q | e
    · change q.1.1.1 = ((xr : ℝ) : EReal) at hx'
      change ((c * δ : ℝ) : EReal) < q.1.1.2
      have hq : D q.1.1 ≠ 0 := by
        intro h0
        have h1 := q.2
        rw [h0] at h1
        simp at h1
      rcases hsep q.1.1 hq with hN | ⟨_, hE⟩
      · have hN' : q.1.1.1 - ((d₁ : ℝ) : EReal) < q.1.1.2 := hN
        rw [hx', ← EReal.coe_sub] at hN'
        exact lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (by linarith)) hN'
      · have hE' : ((d₂ : ℝ) : EReal) < q.1.1.1 := hE
        rw [hx', EReal.coe_lt_coe_iff] at hE'
        exact absurd hE' (by linarith)
    · change e.1 = ((xr : ℝ) : EReal) at hx'
      change ((c * δ : ℝ) : EReal) < e.1
      rw [hx', EReal.coe_lt_coe_iff]
      linarith
  have hy : ((c * δ : ℝ) : EReal) < (pt a).2 := key a hxeq
  have hxQ : ((c * δ : ℝ) : EReal) < (pt a).1 := by
    rw [hxeq, EReal.coe_lt_coe_iff]; linarith
  have hcl1 := (hγ.1 a ⟨hxQ, hy⟩).2
  rw [hab, hpb] at hcl1
  have h3 : (pt a).2 ≤ ((0 : ℝ) : EReal) + ((c * δ : ℝ) : EReal) :=
    le_trans hcl1.1 (add_le_add_left hd _)
  rw [← EReal.coe_add, zero_add] at h3
  exact absurd h3 (not_le.mpr hy)

end

end Aux
end PersistClust.Count

open PersistClust.Count

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : Type*} [MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [RiemannianBundle (fun x : X ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : X ↦ TangentSpace I x)]
    [IsRiemannianManifold I X] [MeasurableSpace X] [BorelSpace X]
    (hconv : 0 < convexityRadius X)
    (f : X → ℝ) (c : ℝ) (hc : 0 < c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (hdens : IsDensity (μH[(Module.finrank ℝ E : ℝ)] : Measure X) f) (htame : IsTame0 f)
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hd : d₁ < d₂) (hsep : IsSeparated (diagram0 f) d₁ d₂)
    (δ : ℝ) (hδ : 0 < δ) (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (hδc : δ < (d₂ - d₁) / (5 * c))
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ)
    (n : ℕ) (pts : Fin n → X) (L : Finset X)
    -- (0) the sample realizes exactly the distinct points of L
    (hmem : ∀ i : Fin n, pts i ∈ L)
    (hsurj : ∀ x ∈ L, ∃ i : Fin n, pts i = x)
    -- (3) the Theorem-4.5 multi-bijection at α = cδ, radius cδ — literally 4_5's γ over L
    (γ : Copies (diagram0 f) ≃
        Copies (ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ))
    (hγ : SatisfiesIIV γ (c * δ) (c * δ)) :
    ∀ σ : Fin n ≃ Fin n, IsSortOrder (f ∘ pts) σ →
      (numClusters (f ∘ pts) (fun i j => dist (pts i) (pts j)) δ τ σ : ℕ∞)
        = prominentCount (diagram0 f) d₂ := by
  classical
  intro σ hσ
  -- (a) M4 (algorithm output): `numClusters` equals the multiplicity of the closed τ-window
  -- of the `n`-point Rips diagram. The distance matrix is symmetric and nonnegative.
  have hcδ : (0 : ℝ) < c * δ := mul_pos hc hδ
  have hτ : (0 : ℝ) < τ := by linarith
  have hM4 : (numClusters (f ∘ pts) (fun i j => dist (pts i) (pts j)) δ τ σ : ℕ∞)
      = {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) <
          ripsDiagram (fun i j => dist (pts i) (pts j)) (f ∘ pts) δ q.1 ∧
          q.1.2 ≤ q.1.1 - ((τ : ℝ) : EReal) ∧ ((τ : ℝ) : EReal) ≤ q.1.1}.encard :=
    proof_thm_4_8_algorithm_output n (f ∘ pts) (fun i j => dist (pts i) (pts j))
      (fun i j => dist_comm (pts i) (pts j)) (fun i j => dist_nonneg)
      δ τ (le_of_lt hδ) hτ σ hσ
  -- (b) lDup: the `n`-point Rips diagram equals the `L`-side (deduplicated) Rips diagram.
  have hLd : ripsDiagram (fun i j => dist (pts i) (pts j)) (f ∘ pts) δ
      = ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ :=
    Aux.ldup_ripsDiagram_eq pts L f δ hmem hsurj (le_of_lt hδ)
  -- (c) Region reconciliation: the closed τ-window (M4's region) equals `Δ^S_τ ∩ Λ^E_τ`
  -- (M3's region). By (b) the two diagrams agree pointwise, and the regions differ only
  -- at bars born exactly at `τ` with death `≤ birth − τ = 0`, where `hτexc` says the
  -- multiplicity is `0` — so no copy lies there.
  have hReg : {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) <
      ripsDiagram (fun i j => dist (pts i) (pts j)) (f ∘ pts) δ q.1 ∧
      q.1.2 ≤ q.1.1 - ((τ : ℝ) : EReal) ∧ ((τ : ℝ) : EReal) ≤ q.1.1}.encard
    = {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) <
      ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ q.1 ∧
      q.1 ∈ DeltaS τ ∩ LamE τ}.encard := by
    refine congrArg (fun s : Set ((EReal × EReal) × ℕ) => s.encard) ?_
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, DeltaS, LamE]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, h2, ?_⟩
      · rw [← congrFun hLd q.1]
        exact h1
      · rcases lt_or_eq_of_le h3 with hlt | heq'
        · exact hlt
        · exfalso
          have heq : q.1.1 = ((τ : ℝ) : EReal) := heq'.symm
          have hz : q.1.2 ≤ ((0 : ℝ) : EReal) := by
            rw [heq] at h2
            rw [← EReal.coe_sub] at h2
            rwa [sub_self] at h2
          have hD0 : ripsDiagram (fun i j => dist (pts i) (pts j)) (f ∘ pts) δ q.1 = 0 := by
            rw [show q.1 = (((τ : ℝ) : EReal), q.1.2) from Prod.ext heq rfl]
            rw [congrFun hLd]
            exact Aux.tau_edge_free (diagram0 f) _ γ c δ hc hδ hγ d₁ d₂ hd₁ hsep τ hτ₁ hτ₂
              q.1.2 hz
          rw [hD0] at h1
          exact absurd h1 (not_lt.mpr (Nat.cast_le.mpr (Nat.zero_le q.2)))
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [congrFun hLd q.1]; exact h1, h2.1, le_of_lt h2.2⟩
  -- (d) M3 (partition count): the `Δ^S_τ ∩ Λ^E_τ` multiplicity of the `L`-side diagram
  -- equals `prominentCount (diagram0 f) d₂`. Both diagrams are `mult` of a rank function,
  -- hence diagram-like.
  have hM3 : {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) <
      ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ q.1 ∧
      q.1 ∈ DeltaS τ ∩ LamE τ}.encard
    = prominentCount (diagram0 f) d₂ :=
    proof_thm_4_8_partition_count (diagram0 f)
      (ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ)
      (Aux.t45gamma_isDiagramLike_mult _) (Aux.t45gamma_isDiagramLike_mult _)
      c δ hc hδ γ hγ d₁ d₂ hd₁ hδc hsep τ hτ₁ hτ₂
  -- Chain the three equalities.
  exact hM4.trans (hReg.trans hM3)
