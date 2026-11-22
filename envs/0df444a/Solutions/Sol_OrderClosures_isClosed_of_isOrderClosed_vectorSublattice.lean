-- Prove2me | solution 1 for OrderClosures.isClosed_of_isOrderClosed_vectorSublattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:13.518954+00:00
-- url     : https://prove2.me/submissions/eb899910-91db-4c24-8f3e-4d147adebb13

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Theorems.Thm_OrderClosures_continuousMap_orderConvergesTo_of_tendsto

set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open OrderClosures
universe u v
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
namespace OrderClosures
theorem _root_.solution
    (Z : VectorSublattice C(K, ℝ))
    (hZ : IsOrderClosed (Z : Set C(K, ℝ))) :
    IsClosed (Z : Set C(K, ℝ)) := by
  apply IsSeqClosed.isClosed
  intro f x hfZ hfx
  apply hZ
  let ι := ULift.{u} ℕ
  let f' : ι → C(K, ℝ) := fun n ↦ f n.down
  have hdown : Filter.Tendsto (fun n : ι ↦ n.down)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 fun n ↦ ?_
    filter_upwards [Filter.eventually_ge_atTop (ULift.up n)] with m hm
    exact hm
  have hf'tend : Filter.Tendsto f' Filter.atTop (nhds x) := by
    exact hfx.comp hdown
  exact ⟨ι, inferInstance, inferInstance, inferInstance, f',
    (fun n ↦ hfZ n.down), continuousMap_orderConvergesTo_of_tendsto hf'tend⟩
end OrderClosures
