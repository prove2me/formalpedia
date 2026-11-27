-- Prove2me | solution 1 for SizeRamsey.Plan.edgeCount_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:22:07.642452+00:00
-- url     : https://prove2.me/submissions/c4e1f36f-9af2-4a37-866a-d3ec5436c17f

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Theorems.Thm_SizeRamsey_edgeCount_eq_card

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    edgeCount G = edgeCount H := by
  rw [edgeCount_eq_card, edgeCount_eq_card]
  exact e.card_edgeFinset_eq
end SizeRamsey.Plan
