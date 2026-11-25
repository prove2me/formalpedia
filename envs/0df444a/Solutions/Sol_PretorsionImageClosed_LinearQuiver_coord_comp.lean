-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.coord_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:39.336498+00:00
-- url     : https://prove2.me/submissions/9f573be3-4ccf-4c8d-81f8-50985937d28f

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_app_val


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
theorem _root_.solution {c d a b a' b' : Fin n} (η : interval k c d ⟶ interval k a b)
    (θ : interval k a b ⟶ interval k a' b') (i : Fin n) :
    coord (η ≫ θ) i = coord η i * coord θ i := by
  unfold coord
  rw [NatTrans.comp_app]
  change ((θ.app i).hom.hom ((η.app i).hom.hom (unit k c d i))).1 = _
  rw [app_val]
  rfl
end PretorsionImageClosed.LinearQuiver
