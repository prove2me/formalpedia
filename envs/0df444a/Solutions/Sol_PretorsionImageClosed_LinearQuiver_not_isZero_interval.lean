-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.not_isZero_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:23:46.306276+00:00
-- url     : https://prove2.me/submissions/7d7c41d9-0a7c-49dd-a910-20fbdb3430a4

module
public import Definitions.Def_PretorsionImageClosed_Biproducts_Basic
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_isZero_iff_subsingleton
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_intervalSpace_of_mem


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
theorem _root_.solution {a d : Fin n} (h : a ≤ d) : ¬ IsZero (interval k a d) := by
  intro hz
  have := hz.obj a
  rw [FGModuleCat.isZero_iff_subsingleton] at this
  change Subsingleton (intervalSpace k a d a) at this
  rw [Submodule.subsingleton_iff_eq_bot, intervalSpace_of_mem k ⟨le_rfl, h⟩] at this
  exact top_ne_bot this
end PretorsionImageClosed.LinearQuiver
