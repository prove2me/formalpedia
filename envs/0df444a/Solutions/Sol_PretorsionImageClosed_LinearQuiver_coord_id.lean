-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.coord_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:27:36.679936+00:00
-- url     : https://prove2.me/submissions/0cecc6be-d5f4-4797-86c2-e0cb358ad93e

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_unit_val


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (a d i : Fin n) : coord (𝟙 (interval k a d)) i = if a ≤ i ∧ i ≤ d then 1 else 0 := by
  unfold coord
  rw [NatTrans.id_app]
  change (unit k a d i : k) = _
  rw [unit_val]
end PretorsionImageClosed.LinearQuiver
