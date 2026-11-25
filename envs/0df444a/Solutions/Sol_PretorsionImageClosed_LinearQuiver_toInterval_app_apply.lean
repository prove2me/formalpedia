-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.toInterval_app_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:16:00.717426+00:00
-- url     : https://prove2.me/submissions/bb9598fe-8b8d-41c0-8f27-35e1d71be958

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
variable (ℓ : Module.Dual k (X.obj d))
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (hfirst : ∀ i, i < i₀ → IsZero (X.obj i)) (j : Fin n) (x : X.obj j) :
    ((toInterval d ℓ hfirst).app j).hom.hom x = toIntervalLin (i₀ := i₀) d ℓ j x := rfl
end PretorsionImageClosed.LinearQuiver
