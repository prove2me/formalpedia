-- Prove2me | solution 1 for SizeRamsey.Plan.tau4_delete_vertices_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:06.255911+00:00
-- url     : https://prove2.me/submissions/795edca5-f168-4207-9646-e4dd47389a24

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_tau4_erase_lift
public import Theorems.Thm_SizeRamsey_exists_transversal_card_eq_tau4
public import Theorems.Thm_SizeRamsey_tau4_le_card


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution
    (D X : Finset V) (hX : X ⊆ D)
    (hHit : HitsDeleted G D X) :
    tau4 G ≤ tau4 (erase G D) + X.card := by
  obtain ⟨T, hT, hcard⟩ := exists_transversal_card_eq_tau4 (erase G D)
  obtain ⟨h1, h2⟩ := tau4_erase_lift G D X hX hHit T hT
  exact (tau4_le_card h1).trans (hcard ▸ h2)
end SizeRamsey.Plan
