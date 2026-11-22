-- Prove2me | solution 1 for OrderClosures.exists_weaklyFatou_not_equivalent_fatou
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:24:16.988164+00:00
-- url     : https://prove2.me/submissions/81b37b85-9855-4736-8736-a4b6beeed1f6

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FinalSpace
public import Theorems.Thm_OrderClosures_finalSpace_weakFatou
public import Theorems.Thm_OrderClosures_finalSpace_not_equivalent_fatou

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
namespace OrderClosures
theorem _root_.solution :
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Lattice X) (_ : IsOrderedAddMonoid X)
      (_ : VectorLattice X),
      ∃ p : PaperLatticeNorm X, IsCompleteFor p ∧ HasWeakFatouProperty p 2 ∧
        ∀ q : PaperLatticeNorm X, HasFatouProperty q → ¬ EquivalentNorms p q := by
  refine ⟨FinalSpace, inferInstance, inferInstance, inferInstance, inferInstance,
    finalLatticeNorm, (finalSpace_weakFatou).1, (finalSpace_weakFatou).2,
    finalSpace_not_equivalent_fatou⟩
end OrderClosures
