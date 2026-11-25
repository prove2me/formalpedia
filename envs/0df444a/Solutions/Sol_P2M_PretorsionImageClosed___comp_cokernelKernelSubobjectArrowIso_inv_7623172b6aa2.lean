-- Prove2me | solution 1 for P2M_PretorsionImageClosed___comp_cokernelKernelSubobjectArrowIso_inv_7623172b6aa2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:52:12.616288+00:00
-- url     : https://prove2.me/submissions/668bffb8-8dc5-4559-aed5-13fa04d91718

module
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Theorems.Thm_P2M_PretorsionImageClosed___comp_cokernelKernelSubobjectArrowIso_hom_4e7f616de0e9
attribute [reassoc (attr := simp)] PretorsionImageClosed.π_comp_cokernelKernelSubobjectArrowIso_hom

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed
theorem _root_.solution {X Q : C} (π : X ⟶ Q) [Epi π] :
    π ≫ (cokernelKernelSubobjectArrowIso π).inv = cokernel.π (kernelSubobject π).arrow := by
  rw [Iso.comp_inv_eq, π_comp_cokernelKernelSubobjectArrowIso_hom]
end PretorsionImageClosed
