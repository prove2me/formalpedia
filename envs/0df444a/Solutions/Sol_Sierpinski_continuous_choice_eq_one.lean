-- Prove2me | solution 1 for Sierpinski.continuous_choice_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:28:52.047024+00:00
-- url     : https://prove2.me/submissions/41e11af2-987a-49f5-9fc3-efcfb40078f0

module
public import Mathlib.Topology.Separation.Regular
public import Definitions.Def_Sierpinski_Solution
public import Theorems.Thm_Sierpinski_exists_eq_univ_of_countable_closed_partition

set_option autoImplicit true
@[expose] public section
public section
open Set
universe u v w
open Sierpinski
variable {X : Type u} [tX : TopologicalSpace X] [t2X : T2Space X]
namespace Sierpinski
theorem _root_.solution [cX : CompactSpace X] [connX : ConnectedSpace X]
    {Y : Type v} [tY : TopologicalSpace Y] [t2Y : T2Space Y]
    {ι : Type w} [countI : Countable ι] (f : ι → X → Y) (g : X → Y)
    (hf : ∀ i, Continuous (f i)) (hg : Continuous g)
    (hdistinct : ∀ x, Pairwise (fun i j => f i x ≠ f j x))
    (hchoice : ∀ x, ∃ i, g x = f i x) : ∃ i, g = f i := by
  let F : ι → Set X := fun i => {x | g x = f i x}
  have hclosed (i : ι) : IsClosed (F i) := isClosed_eq hg (hf i)
  have hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)) := by
    intro i j hij
    exact disjoint_left.mpr fun x hxi hxj => hdistinct x hij (hxi.symm.trans hxj)
  have hcover : ⋃ i, F i = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := hchoice x
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, hi⟩ := exists_eq_univ_of_countable_closed_partition F hclosed hdisjoint hcover
  refine ⟨i, funext fun x => ?_⟩
  exact (show x ∈ F i from hi ▸ mem_univ x)
end Sierpinski
