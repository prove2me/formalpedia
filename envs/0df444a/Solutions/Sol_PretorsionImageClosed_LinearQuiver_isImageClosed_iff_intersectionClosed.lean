-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.isImageClosed_iff_intersectionClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:16:36.492951+00:00
-- url     : https://prove2.me/submissions/0a4c0dc9-ed17-458a-8af4-734413d2a32a

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_intersectionClosed_of_isImageClosed
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_isImageClosed_of_intersectionClosed

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
theorem _root_.solution (C : Subcategory (Statement.LinRep k n)) :
    C.IsImageClosed ↔ IntersectionClosed C :=
  ⟨intersectionClosed_of_isImageClosed C, isImageClosed_of_intersectionClosed C⟩
end PretorsionImageClosed.LinearQuiver
