-- Prove2me | solution 1 for OrderClosures.finiteBandProjection_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:28.238003+00:00
-- url     : https://prove2.me/submissions/b9887b02-0b33-4799-aa1e-e4266ee41180

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
    {w : TreeCoefficients n} (hw : 0 ≤ w) : 0 ≤ finiteBandProjection n Λ w := by
  intro t
  by_cases ht : treeBandOfNode n t ∈ Λ
  · rw [(finiteBandProjection_apply n Λ w t).1 ht]
    exact hw t
  · rw [(finiteBandProjection_apply n Λ w t).2 ht]
    exact le_rfl
end OrderClosures
