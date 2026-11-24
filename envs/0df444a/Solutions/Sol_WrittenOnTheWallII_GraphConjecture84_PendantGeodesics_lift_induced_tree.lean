-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.lift_induced_tree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:18.798253+00:00
-- url     : https://prove2.me/submissions/a16811c6-8bf5-4092-b489-7a94b82766ce

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_induce_union_geodesic_isTree
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_support_disjoint
public import Theorems.Thm_SimpleGraph_card_le_largestInducedTreeSize


set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
open WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)
set_option maxHeartbeats 800000
namespace WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
theorem _root_.solution (hG : G.Connected) (L : ℕ)
    (hLen : ∀ c, (F.path c).length = L)
    (s : Finset ↥(K : Set α))
    (hs : ((G.induce (K : Set α)).induce (s : Set ↥(K : Set α))).IsTree) :
    s.card * (L + 1) ≤ largestInducedTreeSize G := by
  classical
  let B : Finset α := s.image Subtype.val
  let f : ↥(s : Set ↥(K : Set α)) → ↥(B : Set α) := fun x =>
    ⟨((x : ↥(K : Set α)) : α), Finset.mem_image.mpr ⟨x, x.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hval : ((x : ↥(K : Set α)) : α) = ((y : ↥(K : Set α)) : α) :=
        congrArg (fun z : ↥(B : Set α) => (z : α)) hxy
      exact Subtype.ext (Subtype.ext hval)
    · intro y
      obtain ⟨c, hc, hcy⟩ := Finset.mem_image.mp y.property
      exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  let i : ((G.induce (K : Set α)).induce (s : Set ↥(K : Set α))) ≃g
      G.induce (B : Set α) :=
    { Equiv.ofBijective f hf with map_rel_iff' := by intro x y; rfl }
  have hB : (G.induce (B : Set α)).IsTree := i.isTree_iff.mp hs
  let U (t : Finset ↥(K : Set α)) : Finset α :=
    B ∪ t.biUnion (fun c => (F.path c).support.toFinset)
  have hUt : ∀ t : Finset ↥(K : Set α), t ⊆ s → (G.induce (U t : Set α)).IsTree := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      have hUB : U ∅ = B := by simp [U]
      rw [hUB]
      exact hB
    | @insert c t hct ih =>
      intro hts
      have hcs : c ∈ s := hts (Finset.mem_insert_self _ _)
      have hts' : t ⊆ s := fun d hd => hts (Finset.mem_insert_of_mem hd)
      have hroot : (c : α) ∈ U t := Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨c, hcs, rfl⟩)
      have hinter : ∀ z ∈ (F.path c).support, z ∈ U t → z = (c : α) := by
        intro z hz hzU
        rcases Finset.mem_union.mp hzU with hzB | hzt
        · obtain ⟨d, _, hdz⟩ := Finset.mem_image.mp hzB
          exact F.core_inter c z hz (hdz ▸ d.property)
        · obtain ⟨d, hd, hzd⟩ := Finset.mem_biUnion.mp hzt
          have hcd : c ≠ d := fun heq => hct (heq.symm ▸ hd)
          exact ((Finset.disjoint_left.mp (F.support_disjoint hG hcd))
            (List.mem_toFinset.mpr hz) hzd).elim
      have hrev : (F.path c).reverse.length = G.dist (F.endPoint c) c := by
        simpa only [Walk.length_reverse, SimpleGraph.dist_comm] using F.geodesic c
      have hnew := induce_union_geodesic_isTree hG (F.path c).reverse hrev (U t)
        (ih hts') hroot
        (by intro z hz hzu; exact hinter z (by simpa using hz) hzu)
        (by
          intro z hz hzc w hw hzw
          exact hinter w (F.closed c z (by simpa using hz) hzc w hzw) hw)
      have hset : U (insert c t) = (F.path c).reverse.support.toFinset ∪ U t := by
        ext z
        simp [U, or_assoc, or_comm, or_left_comm]
      rw [hset]
      exact hnew
  let T := s.biUnion (fun c => (F.path c).support.toFinset)
  have hUT : U s = T := by
    apply Finset.union_eq_right.mpr
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_biUnion.mpr ⟨c, hc, List.mem_toFinset.mpr (F.path c).start_mem_support⟩
  have hT : (G.induce (T : Set α)).IsTree := hUT ▸ hUt s Finset.Subset.rfl
  have hcardpath (c : ↥(K : Set α)) : (F.path c).support.toFinset.card = L + 1 := by
    rw [List.toFinset_card_of_nodup ((F.path c).isPath_of_length_eq_dist
      (F.geodesic c)).support_nodup, Walk.length_support, hLen c]
  have hcard : T.card = s.card * (L + 1) := by
    rw [Finset.card_biUnion]
    · simp only [hcardpath, Finset.sum_const, smul_eq_mul]
    · intro c hc d hd hcd
      exact F.support_disjoint hG hcd
  rw [← hcard]
  exact card_le_largestInducedTreeSize hT
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
