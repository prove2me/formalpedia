-- Prove2me | solution 1 for PebblingLean.Pebbling.supportSize_mul_minPileCost_le_size_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:12.322617+00:00
-- url     : https://prove2.me/submissions/3d44ebba-ecd8-40e0-97a4-673f9fc1c431

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Theorems.Thm_PebblingLean_Pebbling_supportSize_mul_le_size_of_minOccupiedPileSize

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [Fintype V]
    {D : Pebbling V} {S K : ℕ} (hmin : MinOccupiedPileSize D S) :
    supportSize D * (S * K) ≤ size D * K := by
  rw [← Nat.mul_assoc]
  exact Nat.mul_le_mul_right K
    (supportSize_mul_le_size_of_minOccupiedPileSize hmin)
end PebblingLean.Pebbling
