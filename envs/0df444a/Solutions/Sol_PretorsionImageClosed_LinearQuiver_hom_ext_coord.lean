-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.hom_ext_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:35.744218+00:00
-- url     : https://prove2.me/submissions/2c80f1ff-38d5-4767-93ae-e02e5db14370

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
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
variable (k : Type u) [Field k] {n : ℕ}
variable {k}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {c d a b : Fin n} {η η' : interval k c d ⟶ interval k a b}
    (h : ∀ i, coord η i = coord η' i) : η = η' := by
  ext i : 2
  apply FGModuleCat.hom_ext
  refine LinearMap.ext fun (x : intervalSpace k c d i) => ?_
  apply Subtype.ext
  change ((η.app i).hom.hom x).1 = ((η'.app i).hom.hom x).1
  rw [app_val, app_val, h]
end PretorsionImageClosed.LinearQuiver
