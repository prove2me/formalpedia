-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.coord_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:29:35.795187+00:00
-- url     : https://prove2.me/submissions/97a74a3b-3a68-419c-bd33-176092964a28

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables

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
theorem _root_.solution (c d a b i : Fin n) : coord (0 : interval k c d ⟶ interval k a b) i = 0 := by
  unfold coord
  change ((0 : (interval k c d).obj i ⟶ (interval k a b).obj i).hom.hom (unit k c d i)).1 = 0
  rfl
end PretorsionImageClosed.LinearQuiver
