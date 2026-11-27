-- Prove2me | solution 1 for SizeRamsey.Plan.erase_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:53.408412+00:00
-- url     : https://prove2.me/submissions/480c29f4-4a91-4d8b-a5d8-0913501158b5

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution
    {V : Type u} [Fintype V] (D : Finset V) :
    Fintype.card {x : V // x ∉ D} + D.card =
      Fintype.card V := by
  rw [Fintype.card_subtype_compl, Fintype.card_coe]
  have := Finset.card_le_univ D
  omega
end SizeRamsey.Plan
