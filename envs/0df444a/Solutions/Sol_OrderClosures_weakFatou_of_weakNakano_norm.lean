-- Prove2me | solution 1 for OrderClosures.weakFatou_of_weakNakano_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:48.891402+00:00
-- url     : https://prove2.me/submissions/673f2703-7a04-4c1d-a7aa-b4595e36bd55

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
public import Theorems.Thm_OrderClosures_weakFatou_of_weakNakano_p

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
    [NormedVectorLattice Y] {K : ℝ}
    (hNak : IsWeakNakanoConstant (X := Y) norm K) :
    HasWeakFatouProperty (norm : Y → ℝ) K := by
  exact weakFatou_of_weakNakano_p ambientLatticeNorm hNak
end OrderClosures
