-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.imageSubobject_intervalIncl_comp_intervalProj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:35:22.6168+00:00
-- url     : https://prove2.me/submissions/799244e6-79cd-4a63-839b-9bdacb058d19

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalTraceReject
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_imageSubobject_canonicalHom


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Subcategory
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {c u ℓ d : Fin n} (hcu : c ≤ u) (hℓd : ℓ ≤ d) :
    imageSubobject (intervalIncl k d hcu ≫ intervalProj k c hℓd) = suffix c ℓ u hcu := by
  rw [intervalIncl_comp_intervalProj, imageSubobject_canonicalHom]
  rfl
end PretorsionImageClosed.LinearQuiver
