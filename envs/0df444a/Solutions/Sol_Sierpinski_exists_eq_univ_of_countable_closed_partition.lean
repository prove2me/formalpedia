-- Prove2me | solution 1 for Sierpinski.exists_eq_univ_of_countable_closed_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:20:11.204667+00:00
-- url     : https://prove2.me/submissions/5c288cb1-b54c-4e4b-b084-b3591e0648d9

module
public import Mathlib.Topology.Separation.Regular
public import Definitions.Def_Sierpinski_Solution
public import Theorems.Thm_Sierpinski_exists_eq_univ_of_nat_closed_partition

set_option autoImplicit true
@[expose] public section
public section
open Set
universe u v w
open Sierpinski
variable {X : Type u} [tX : TopologicalSpace X] [t2X : T2Space X]
namespace Sierpinski
theorem _root_.solution
    [cX : CompactSpace X] [connX : ConnectedSpace X] {ι : Type v} [countI : Countable ι]
    (F : ι → Set X) (hclosed : ∀ i, IsClosed (F i))
    (hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcover : ⋃ i, F i = univ) : ∃ i, F i = univ := by
  classical
  obtain ⟨e, he⟩ := exists_injective_nat ι
  let G : ℕ → Set X := fun n => ⋃ i, ⋃ (_ : e i = n), F i
  have hGat (i : ι) : G (e i) = F i := by
    ext x
    simp only [G, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨j, hj, hxj⟩
      exact he hj ▸ hxj
    · intro hxi
      exact ⟨i, rfl, hxi⟩
  have hGempty (n : ℕ) (hn : ¬ ∃ i, e i = n) : G n = ∅ := by
    ext x
    simp only [G, mem_iUnion, exists_prop, mem_empty_iff_false, iff_false]
    rintro ⟨i, hi, _⟩
    exact hn ⟨i, hi⟩
  have hGclosed (n : ℕ) : IsClosed (G n) := by
    by_cases hn : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := hn
      rw [hGat]
      exact hclosed i
    · rw [hGempty n hn]
      exact isClosed_empty
  have hGdisjoint : Pairwise (fun m n => Disjoint (G m) (G n)) := by
    intro m n hmn
    refine disjoint_left.mpr ?_
    intro x hxm hxn
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxm
    obtain ⟨him, hxi⟩ := mem_iUnion.mp hxi
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxn
    obtain ⟨hjn, hxj⟩ := mem_iUnion.mp hxj
    have hij : i ≠ j := by
      intro hij
      exact hmn (him.symm.trans (hij ▸ hjn))
    exact disjoint_left.mp (hdisjoint hij) hxi hxj
  have hGcover : ⋃ n, G n = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover ▸ mem_univ x)
    exact mem_iUnion.mpr ⟨e i, hGat i ▸ hxi⟩
  obtain ⟨n, hn⟩ := exists_eq_univ_of_nat_closed_partition G hGclosed hGdisjoint hGcover
  have hindex : ∃ i, e i = n := by
    by_contra hnindex
    have : (univ : Set X) = ∅ := hn.symm.trans (hGempty n hnindex)
    exact univ_nonempty.ne_empty this
  obtain ⟨i, rfl⟩ := hindex
  exact ⟨i, (hGat i).symm.trans hn⟩
end Sierpinski
