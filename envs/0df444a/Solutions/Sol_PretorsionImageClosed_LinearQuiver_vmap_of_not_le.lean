-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.vmap_of_not_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:01:47.034603+00:00
-- url     : https://prove2.me/submissions/5f5e6df0-5247-4f52-8001-a308b351fd43

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
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {j : Fin n} (h : ¬ i₀ ≤ j) : vmap X i₀ v j = 0 := by
  unfold vmap
  rw [dif_neg h]
end PretorsionImageClosed.LinearQuiver
