-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.reachable_compl_of_mem_geodesic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:23:33.467183+00:00
-- url     : https://prove2.me/submissions/d99f9dba-9371-4210-8c3c-31afeb56bc5b

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} {c a z : α}
    (p : G.Walk c a) (hp : p.length = G.dist c a) (ha : a ≠ c)
    (hz : z ∈ p.support) (hzc : z ≠ c) :
    (G.induce ({c}ᶜ : Set α)).Reachable
      ⟨z, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzc⟩
      ⟨a, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ha⟩ := by
  cases p with
  | nil => exact (ha rfl).elim
  | @cons c n a hcn p =>
    have hpath := (p.cons hcn).isPath_of_length_eq_dist hp
    have hcnot : c ∉ p.support := (List.nodup_cons.mp hpath.support_nodup).1
    have hzp : z ∈ p.support := by
      simpa only [Walk.support_cons, List.mem_cons, or_iff_right hzc] using hz
    let q := p.dropUntil z hzp
    have hsub : ∀ w ∈ q.support, w ∈ ({c}ᶜ : Set α) := by
      intro w hw
      have hwp := p.support_dropUntil_subset hzp hw
      have hwc : w ≠ c := by intro heq; exact hcnot (heq ▸ hwp)
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hwc
    exact ⟨q.induce ({c}ᶜ : Set α) hsub⟩
end WrittenOnTheWallII.GraphConjecture84
