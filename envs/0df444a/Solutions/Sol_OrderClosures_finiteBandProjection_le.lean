-- Prove2me | solution 1 for OrderClosures.finiteBandProjection_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:28.822424+00:00
-- url     : https://prove2.me/submissions/d96c5ce9-d558-4c46-bf3d-5a31de1cc7a8

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
public import Theorems.Thm_OrderClosures_finiteBandProjection_apply

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
namespace OrderClosures
theorem _root_.solution (n : ℕ) (Λ : Finset (TreeBandIndex n))
    {w : TreeCoefficients n} (hw : 0 ≤ w) : finiteBandProjection n Λ w ≤ w := by
  intro t
  by_cases ht : treeBandOfNode n t ∈ Λ
  · rw [(finiteBandProjection_apply n Λ w t).1 ht]
  · rw [(finiteBandProjection_apply n Λ w t).2 ht]
    exact hw t
end OrderClosures
