-- Prove2me | solution 1 for OrderClosures.regularOpenOfClopen_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:27.815777+00:00
-- url     : https://prove2.me/submissions/739ee5a8-ca5a-4600-937c-a73b018711f6

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Theorems.Thm_OrderClosures_regularOpen_ext

set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open OrderClosures
universe u
namespace OrderClosures
theorem _root_.solution {X : Type u} [TopologicalSpace X]
    (s t : Set X) (hs : IsClopen s) (ht : IsClopen t) :
    regularOpenOfClopen (s ∩ t) (hs.inter ht) =
      regularOpenOfClopen s hs ⊓ regularOpenOfClopen t ht := by
  apply regularOpen_ext
  rfl
end OrderClosures
