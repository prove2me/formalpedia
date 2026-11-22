-- Prove2me | solution 1 for OrderClosures.isOrderComplete_continuousMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:12.741482+00:00
-- url     : https://prove2.me/submissions/bb25645a-bd0f-4272-9397-b0baa2df9cd2

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Theorems.Thm_OrderClosures_continuousFamilySup_isLUB

set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open OrderClosures
universe u
variable (K : Type u) [TopologicalSpace K] [ExtremallyDisconnected K]
namespace OrderClosures
theorem _root_.solution : IsOrderComplete C(K, ℝ) := by
  intro A hA hAbdd
  exact ⟨continuousFamilySup K A hA hAbdd,
    continuousFamilySup_isLUB K A hA hAbdd⟩
end OrderClosures
