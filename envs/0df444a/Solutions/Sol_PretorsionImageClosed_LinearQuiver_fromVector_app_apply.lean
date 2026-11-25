-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.fromVector_app_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:02:40.965142+00:00
-- url     : https://prove2.me/submissions/572d199e-f932-493c-9126-40d7eff5ecf4

module
public import Definitions.Def_PretorsionImageClosed_Biproducts_Basic
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition

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
variable (X : Statement.LinRep k n) (i₀ : Fin n) (v : X.obj i₀)
variable {X i₀ v} (d : Fin n)
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (hd : ∀ j, d < j → vmap X i₀ v j = 0) (j : Fin n)
    (x : intervalSpace k i₀ d j) :
    ((fromVector d hd).app j).hom.hom x = (x : k) • vmap X i₀ v j := rfl
end PretorsionImageClosed.LinearQuiver
