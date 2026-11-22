-- Prove2me | solution 1 for OrderClosures.separable_weakSequentialNakano_implies_weakNakano
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:58.789914+00:00
-- url     : https://prove2.me/submissions/1b8a4d36-413c-43b7-a97a-62821c16f234

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
public import Theorems.Thm_OrderClosures_weakNakano_of_weakSequentialNakano
public import Theorems.Thm_OrderClosures_weakFatou_of_weakNakano_norm

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace OrderClosures
theorem _root_.solution
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] [TopologicalSpace.SeparableSpace Y]
    {K : ℝ}
    (hseq : IsWeakSequentialNakanoConstant (X := Y) norm K) :
    IsWeakNakanoConstant (X := Y) norm K ∧
      HasWeakFatouProperty (norm : Y → ℝ) K := by
  have hNak := weakNakano_of_weakSequentialNakano hseq
  exact ⟨hNak, weakFatou_of_weakNakano_norm hNak⟩
end OrderClosures
