-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.intersectionClosed_of_isImageClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:13:12.877919+00:00
-- url     : https://prove2.me/submissions/9a918a20-4666-412a-a6b8-28ecd22f42f6

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_prop_interval_of_prop_suffix
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_imageSubobject_canonicalHom


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (C : Subcategory (Statement.LinRep k n))
    (hC : C.IsImageClosed) : IntersectionClosed C := by
  intro a b c d hab hcd ha hc hmin
  -- by symmetry, assume `a ≤ c`
  wlog hac : a ≤ c generalizing a b c d
  · have := this c d a b hcd hab hc ha (by rwa [max_comm, min_comm]) (le_of_not_ge hac)
    rwa [max_comm, min_comm] at this
  rw [max_eq_right hac]
  rcases le_total d b with hdb | hbd
  · rw [min_eq_right hdb]
    exact hc
  · rw [min_eq_left hbd]
    -- the image of the canonical morphism `M_{c,d} ⟶ M_{a,b}` is `M_{c,b}`
    have himg := Statement.IsImageClosed.prop_imageSubobject hC (canonicalHom (k := k) hac hbd) hc ha
    rw [imageSubobject_canonicalHom] at himg
    exact prop_interval_of_prop_suffix C hac himg
end PretorsionImageClosed.LinearQuiver
