-- Prove2me | solution 1 for OrderClosures.regularOpen_ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:56:58.762827+00:00
-- url     : https://prove2.me/submissions/4db97463-8e50-4520-88e7-69421fd066ea

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay

set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open OrderClosures
universe u
namespace OrderClosures
theorem _root_.solution {X : Type u} [TopologicalSpace X]
    {U V : RegularOpen X}
    (h : (((U : TopologicalSpace.Opens X) : Set X)) =
      (((V : TopologicalSpace.Opens X) : Set X))) : U = V := by
  apply Heyting.Regular.coe_injective
  exact TopologicalSpace.Opens.ext h
end OrderClosures
