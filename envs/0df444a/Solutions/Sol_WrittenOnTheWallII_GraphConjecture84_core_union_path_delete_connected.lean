-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.core_union_path_delete_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:35:09.364212+00:00
-- url     : https://prove2.me/submissions/452fab6a-34ce-48d8-9b96-6735ec707002

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_reachable_induce_delete_of_walk
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_exists_walk_in_core_avoiding

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
set_option maxHeartbeats 800000
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (K : Finset α)
    (hcard : 3 ≤ K.card) (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    {a b : α} (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b)
    (p : G.Walk a b) (hp : p.IsPath)
    (x : ↥((K ∪ p.support.toFinset : Finset α) : Set α)) :
    ((G.induce ((K ∪ p.support.toFinset : Finset α) : Set α)).induce
      ({x}ᶜ : Set ↥((K ∪ p.support.toFinset : Finset α) : Set α))).Connected := by
  classical
  let U : Set α := (K ∪ p.support.toFinset : Finset α)
  have hyex : ∃ y ∈ K, y ≠ (x : α) := by
    by_contra! hn
    have hsub : K ⊆ {(x : α)} := by intro y hy; simpa using hn y hy
    have hle := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hle
    omega
  obtain ⟨y, hy, hyx⟩ := hyex
  let y' : ↥({x}ᶜ : Set U) := ⟨⟨y, Finset.mem_union_left _ hy⟩, by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro heq
    exact hyx (congrArg Subtype.val heq)⟩
  have hcore (z : α) (hz : z ∈ K) (hzx : z ≠ (x : α)) :
      ∃ q : G.Walk y z, (∀ w ∈ q.support, w ∈ U) ∧ (x : α) ∉ q.support := by
    obtain ⟨q, hq, hqx⟩ := exists_walk_in_core_avoiding K hK hdel (x : α) hy hz hyx hzx
    exact ⟨q, fun w hw => Finset.mem_union_left _ (hq w hw), hqx⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨y', ?_⟩
  intro z
  have hzx : ((z : U) : α) ≠ (x : α) := by
    intro heq
    have hne : (z : U) ≠ x := z.property
    exact hne (Subtype.ext heq)
  have hzU : ((z : U) : α) ∈ K ∪ p.support.toFinset := (z : U).property
  rcases Finset.mem_union.mp hzU with hzK | hzp
  · obtain ⟨q, hq, hqx⟩ := hcore _ hzK hzx
    exact reachable_induce_delete_of_walk x y' z q hq hqx
  · have hzp' : ((z : U) : α) ∈ p.support := List.mem_toFinset.mp hzp
    let pa := p.takeUntil ((z : U) : α) hzp'
    let pb := p.dropUntil ((z : U) : α) hzp'
    have hpath : (pa.append pb).IsPath := by rw [p.take_spec hzp']; exact hp
    have hprefix : ∀ w ∈ pa.support, w ∈ U := by
      intro w hw
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr (p.support_takeUntil_subset hzp' hw))
    have hsuffix : ∀ w ∈ pb.support, w ∈ U := by
      intro w hw
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr (p.support_dropUntil_subset hzp' hw))
    by_cases hxa : (x : α) ∈ pa.support
    · have hxb : (x : α) ∉ pb.support := by
        intro hxb
        exact hpath.ne_of_mem_support_of_append hzx.symm hxa hxb rfl
      have hbx : b ≠ (x : α) := by intro heq; exact hxb (heq ▸ pb.end_mem_support)
      obtain ⟨q, hq, hqx⟩ := hcore b hb hbx
      let r := q.append pb.reverse
      have hrU : ∀ w ∈ r.support, w ∈ U := by
        intro w hw
        have hsup : w ∈ q.support ∨ w ∈ pb.support := by
          simp only [r, Walk.support_append, List.mem_append] at hw
          rcases hw with hw | hw
          · exact Or.inl hw
          · exact Or.inr (by simpa only [Walk.support_reverse, List.mem_reverse] using
              List.mem_of_mem_tail hw)
        exact hsup.elim (hq w) (hsuffix w)
      have hrx : (x : α) ∉ r.support := by
        intro hxmem
        have hsup : (x : α) ∈ q.support ∨ (x : α) ∈ pb.support := by
          simp only [r, Walk.support_append, List.mem_append] at hxmem
          rcases hxmem with hxmem | hxmem
          · exact Or.inl hxmem
          · exact Or.inr (by simpa only [Walk.support_reverse, List.mem_reverse] using
              List.mem_of_mem_tail hxmem)
        exact hsup.elim hqx hxb
      exact reachable_induce_delete_of_walk x y' z r hrU hrx
    · have hax : a ≠ (x : α) := by intro heq; exact hxa (heq ▸ pa.start_mem_support)
      obtain ⟨q, hq, hqx⟩ := hcore a ha hax
      let r := q.append pa
      have hrU : ∀ w ∈ r.support, w ∈ U := by
        intro w hw
        have hsup : w ∈ q.support ∨ w ∈ pa.support := by
          simp only [r, Walk.support_append, List.mem_append] at hw
          exact hw.elim Or.inl (fun hw => Or.inr (List.mem_of_mem_tail hw))
        exact hsup.elim (hq w) (hprefix w)
      have hrx : (x : α) ∉ r.support := by
        intro hxmem
        have hsup : (x : α) ∈ q.support ∨ (x : α) ∈ pa.support := by
          simp only [r, Walk.support_append, List.mem_append] at hxmem
          exact hxmem.elim Or.inl (fun hw => Or.inr (List.mem_of_mem_tail hw))
        exact hsup.elim hqx hxa
      exact reachable_induce_delete_of_walk x y' z r hrU hrx
end WrittenOnTheWallII.GraphConjecture84
