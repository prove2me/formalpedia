-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.cycle_support_delete_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:35:04.755805+00:00
-- url     : https://prove2.me/submissions/4dafe260-d91e-4898-84a0-2ce51df025ac

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_end_not_mem_takeUntil

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} {u : α} (p : G.Walk u u)
    (hp : p.IsCycle) (x : ↥(p.support.toFinset : Set α)) :
    ((G.induce (p.support.toFinset : Set α)).induce ({x}ᶜ : Set ↥(p.support.toFinset : Set α))).Connected := by
  classical
  have hx : (x : α) ∈ p.support := List.mem_toFinset.mp x.property
  let r := p.rotate (x : α) hx
  have hr : r.IsCycle := hp.rotate hx
  have hrtail : r.tail.IsPath := by
    rw [Walk.isPath_def, r.support_tail_of_not_nil hr.not_nil]
    exact hr.support_nodup
  have hrot (z : α) (hz : z ∈ r.support) : z ∈ p.support :=
    (p.mem_support_rotate_iff (x : α) hx).mp hz
  have htailmem (z : α) (hz : z ∈ p.support) (hzx : z ≠ (x : α)) :
      z ∈ r.tail.support := by
    rw [r.support_tail_of_not_nil hr.not_nil]
    have hzr := (p.mem_support_rotate_iff (x : α) hx).mpr hz
    have hhead : r.support = (x : α) :: r.support.tail := by cases r <;> rfl
    rw [hhead] at hzr
    exact (List.mem_cons.mp hzr).resolve_left hzx
  let S : Set α := p.support.toFinset
  let T : Set α := {z | z ∈ S ∧ z ≠ (x : α)}
  let f : G.induce T →g (G.induce S).induce ({x}ᶜ : Set S) :=
    { toFun := fun z => ⟨⟨z, z.property.1⟩, by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro heq
        exact z.property.2 (congrArg Subtype.val heq)⟩
      map_rel' := by intro a b hab; exact hab }
  have hnmem : r.snd ∈ S := by
    apply List.mem_toFinset.mpr
    exact hrot _ (r.getVert_mem_support 1)
  have hnx : r.snd ≠ (x : α) := (r.adj_snd hr.not_nil).ne.symm
  let n : ↥({x}ᶜ : Set S) := ⟨⟨r.snd, hnmem⟩, by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro heq
    exact hnx (congrArg Subtype.val heq)⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨n, ?_⟩
  intro z
  have hzmem : ((z : S) : α) ∈ p.support := by
    exact List.mem_toFinset.mp (z : S).property
  have hzx : ((z : S) : α) ≠ (x : α) := by
    intro heq
    have hne : (z : S) ≠ x := z.property
    exact hne (Subtype.ext heq)
  have hztail := htailmem _ hzmem hzx
  let q := r.tail.takeUntil ((z : S) : α) hztail
  have hqx : (x : α) ∉ q.support := end_not_mem_takeUntil r.tail hrtail hztail hzx
  have hsub : ∀ w ∈ q.support, w ∈ T := by
    intro w hw
    have hwrtail : w ∈ r.tail.support := r.tail.support_takeUntil_subset hztail hw
    have hwr : w ∈ r.support := by
      rw [r.support_tail_of_not_nil hr.not_nil] at hwrtail
      exact List.mem_of_mem_tail hwrtail
    refine ⟨List.mem_toFinset.mpr (hrot w hwr), ?_⟩
    intro heq
    exact hqx (heq ▸ hw)
  exact ⟨(q.induce T hsub).map f⟩
end WrittenOnTheWallII.GraphConjecture84
