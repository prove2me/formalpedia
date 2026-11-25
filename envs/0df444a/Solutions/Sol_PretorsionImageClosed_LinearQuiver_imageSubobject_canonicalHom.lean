-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.imageSubobject_canonicalHom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:08:05.967132+00:00
-- url     : https://prove2.me/submissions/7a144549-3839-4b2b-be70-74a996d77916

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_canonicalHom_eq
public import Theorems.Thm_PretorsionImageClosed_imageSubobject_epi_comp


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
theorem _root_.solution {c d a b : Fin n} (hac : a ≤ c) (hbd : b ≤ d) :
    imageSubobject (canonicalHom (k := k) hac hbd) = Subobject.mk (intervalIncl k b hac) := by
  rw [canonicalHom_eq, imageSubobject_epi_comp, imageSubobject_mono]
end PretorsionImageClosed.LinearQuiver
