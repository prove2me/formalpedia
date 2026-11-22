-- Prove2me | solution 1 for OrderClosures.booleanStoneClopen_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:37.596705+00:00
-- url     : https://prove2.me/submissions/42879c2f-030e-46cb-93e1-ab32c18a2a9d

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
variable (B : Type u) [BooleanAlgebra B]
namespace OrderClosures
theorem _root_.solution :
    Function.Injective (booleanStoneClopen B) := by
  intro a b hab
  apply le_antisymm
  · exact booleanStoneClopen_subset_iff B |>.mp (by rw [hab])
  · exact booleanStoneClopen_subset_iff B |>.mp (by rw [hab])
end OrderClosures
