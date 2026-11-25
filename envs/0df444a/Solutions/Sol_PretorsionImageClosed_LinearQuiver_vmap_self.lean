-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.vmap_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:27.472646+00:00
-- url     : https://prove2.me/submissions/870c770e-fcc8-4b62-94f6-ce713163557a

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
theorem _root_.solution : vmap X i₀ v i₀ = v := by
  rw [vmap_of_le X i₀ v le_rfl]
  change (X.map (𝟙 i₀)).hom.hom v = v
  rw [X.map_id]
  rfl
end PretorsionImageClosed.LinearQuiver
