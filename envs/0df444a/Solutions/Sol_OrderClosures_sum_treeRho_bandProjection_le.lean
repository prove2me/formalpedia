-- Prove2me | solution 1 for OrderClosures.sum_treeRho_bandProjection_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:17.769977+00:00
-- url     : https://prove2.me/submissions/2bcdc90d-5fc7-470a-9bbb-b27d10cbca32

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
public import Theorems.Thm_OrderClosures_treeRho_finiteBandProjection
public import Theorems.Thm_OrderClosures_treeRho_finiteBandProjection_le

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
namespace OrderClosures
theorem _root_.solution (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) (w : TreeCoefficients n) :
    ∑ B ∈ Λ, treeRho n (treeBandProjection n B w) ≤ treeRho n w := by
  rw [← treeRho_finiteBandProjection]
  exact treeRho_finiteBandProjection_le n Λ w
end OrderClosures
